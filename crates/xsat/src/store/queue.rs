use crate::{
    solver::{literal, Solver},
    store::convert::widen,
};

const DISCONNECT: u32 = u32::MAX;

fn disconnected(idx: u32) -> bool {
    i32::try_from(idx).is_err()
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Links {
    prev: u32,
    next: u32,
    pub(crate) stamp: u32,
}

impl Default for Links {
    fn default() -> Links {
        Links {
            prev: DISCONNECT,
            next: DISCONNECT,
            stamp: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Queue {
    pub(crate) links: Vec<Links>,
    first: u32,
    last: u32,
    stamp: u32,
    pub(crate) search_idx: u32,
    pub(crate) search_stamp: u32,
}

impl Default for Queue {
    fn default() -> Queue {
        Queue {
            links: Vec::new(),
            first: DISCONNECT,
            last: DISCONNECT,
            stamp: 0,
            search_idx: DISCONNECT,
            search_stamp: 0,
        }
    }
}

impl Queue {
    pub(crate) fn update(&mut self, idx: u32) {
        self.search_idx = idx;
        self.search_stamp = self.links[widen(idx)].stamp;
    }

    pub(crate) fn prev(&self, idx: u32) -> u32 {
        self.links[widen(idx)].prev
    }

    fn enqueue_links(&mut self, idx: u32) {
        let last = self.last;
        self.links[widen(idx)].prev = last;
        self.last = idx;
        if disconnected(last) {
            self.first = idx;
        } else {
            self.links[widen(last)].next = idx;
        }
        if self.stamp == u32::MAX {
            self.reassign_stamps();
        } else {
            self.stamp += 1;
            self.links[widen(idx)].stamp = self.stamp;
        }
    }

    fn dequeue_links(&mut self, idx: u32) {
        let Links { prev, next, .. } = self.links[widen(idx)];
        self.links[widen(idx)].prev = DISCONNECT;
        self.links[widen(idx)].next = DISCONNECT;
        if disconnected(prev) {
            self.first = next;
        } else {
            self.links[widen(prev)].next = next;
        }
        if disconnected(next) {
            self.last = prev;
        } else {
            self.links[widen(next)].prev = prev;
        }
    }

    pub(crate) fn dequeue(&mut self, idx: u32) {
        if self.search_idx == idx {
            let links = self.links[widen(idx)];
            let search = if links.next == DISCONNECT {
                links.prev
            } else {
                links.next
            };
            if search == DISCONNECT {
                self.search_idx = DISCONNECT;
                self.search_stamp = 0;
            } else {
                self.update(search);
            }
        }
        self.dequeue_links(idx);
    }

    pub(crate) fn reset_search(&mut self) {
        self.update(self.last);
    }

    pub(crate) fn compact(&mut self, map: &[Option<u32>]) {
        let mapped = |idx: u32| map[widen(idx)].unwrap_or(DISCONNECT);
        self.stamp = 0;
        let mut prev = DISCONNECT;
        let mut previous_old = None;
        let mut idx = self.first;
        while !disconnected(idx) {
            let midx = mapped(idx);
            self.stamp += 1;
            let links = &mut self.links[widen(idx)];
            links.prev = prev;
            links.stamp = self.stamp;
            if idx == self.search_idx {
                self.search_idx = midx;
                self.search_stamp = self.stamp;
            }
            match previous_old {
                None => self.first = midx,
                Some(old) => self.links[widen(old)].next = midx,
            }
            prev = midx;
            previous_old = Some(idx);
            idx = self.links[widen(idx)].next;
        }
        self.last = prev;
        match previous_old {
            None => self.first = DISCONNECT,
            Some(old) => self.links[widen(old)].next = DISCONNECT,
        }
        for (old, &midx) in map.iter().enumerate() {
            if let Some(midx) = midx {
                self.links[widen(midx)] = self.links[old];
            }
        }
    }

    pub(crate) fn move_fresh_to_front(&mut self, fresh: &[u32]) {
        for &idx in fresh {
            self.dequeue_links(idx);
        }
        for &idx in fresh {
            if disconnected(self.first) {
                self.last = idx;
            } else {
                self.links[widen(self.first)].prev = idx;
            }
            self.links[widen(idx)].next = self.first;
            self.first = idx;
        }
        self.stamp = 0;
        let mut idx = self.first;
        while !disconnected(idx) {
            self.stamp += 1;
            self.links[widen(idx)].stamp = self.stamp;
            idx = self.links[widen(idx)].next;
        }
        self.search_idx = self.last;
        self.search_stamp = self.stamp;
    }

    fn reassign_stamps(&mut self) {
        self.stamp = 0;
        let mut idx = self.first;
        while !disconnected(idx) {
            self.stamp += 1;
            self.links[widen(idx)].stamp = self.stamp;
            idx = self.links[widen(idx)].next;
        }
        if !disconnected(self.search_idx) {
            self.search_stamp = self.links[widen(self.search_idx)].stamp;
        }
    }
}

impl Solver {
    pub(crate) fn enqueue(&mut self, idx: u32) {
        let queue = &mut self.queue;
        queue.links[widen(idx)] = Links::default();
        queue.enqueue_links(idx);
        if self.assignment.values[widen(literal(idx))] == 0 {
            queue.update(idx);
        }
    }

    pub(crate) fn move_to_front(&mut self, idx: u32) {
        let queue = &mut self.queue;
        if idx == queue.last {
            return;
        }
        let assigned = self.assignment.values[widen(literal(idx))] != 0;
        if assigned && queue.search_idx == idx {
            let Links { prev, next, .. } = queue.links[widen(idx)];
            queue.update(if disconnected(prev) { next } else { prev });
        }
        queue.dequeue_links(idx);
        queue.enqueue_links(idx);
        if !assigned {
            queue.update(idx);
        }
    }
}
