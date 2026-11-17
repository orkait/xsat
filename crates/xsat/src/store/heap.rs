use crate::store::convert::{narrow, widen};

const ABSENT: u32 = u32::MAX;

#[derive(Clone, Debug, Default)]
pub(crate) struct Heap {
    tainted: bool,
    stack: Vec<u32>,
    score: Vec<f64>,
    pos: Vec<u32>,
}

impl Heap {
    pub(crate) fn vars(&self) -> u32 {
        narrow(self.pos.len())
    }

    pub(crate) fn contains(&self, idx: u32) -> bool {
        self.pos
            .get(widen(idx))
            .is_some_and(|&at| i32::try_from(at).is_ok())
    }

    pub(crate) fn score(&self, idx: u32) -> f64 {
        self.score.get(widen(idx)).copied().unwrap_or(0.0)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub(crate) fn max(&self) -> u32 {
        self.stack[0]
    }

    pub(crate) fn max_score(&self) -> f64 {
        if !self.tainted {
            return 0.0;
        }
        self.score
            .iter()
            .copied()
            .reduce(|best, score| if score > best { score } else { best })
            .unwrap_or(0.0)
    }

    pub(crate) fn enlarge(&mut self, vars: u32) {
        let vars = widen(vars);
        if vars > self.pos.len() {
            self.pos.resize(vars, ABSENT);
            self.score.resize(vars, 0.0);
        }
    }

    fn import(&mut self, idx: u32) {
        if self.vars() <= idx {
            self.enlarge(idx + 1);
        }
    }

    pub(crate) fn push(&mut self, idx: u32) {
        self.import(idx);
        self.pos[widen(idx)] = narrow(self.stack.len());
        self.stack.push(idx);
        self.bubble_up(idx);
    }

    pub(crate) fn pop(&mut self, idx: u32) {
        let Some(last) = self.stack.pop() else {
            return;
        };
        self.pos[widen(last)] = ABSENT;
        if last == idx {
            return;
        }
        let idx_pos = self.pos[widen(idx)];
        self.pos[widen(idx)] = ABSENT;
        self.stack[widen(idx_pos)] = last;
        self.pos[widen(last)] = idx_pos;
        self.bubble_up(last);
        self.bubble_down(last);
    }

    pub(crate) fn pop_max(&mut self) -> u32 {
        let idx = self.stack[0];
        let last = self.stack.pop().unwrap_or(idx);
        self.pos[widen(last)] = ABSENT;
        if last == idx {
            return idx;
        }
        self.pos[widen(idx)] = ABSENT;
        self.stack[0] = last;
        self.pos[widen(last)] = 0;
        self.bubble_down(last);
        idx
    }

    #[expect(
        clippy::float_cmp,
        reason = "Kissat skips the update only for the bit-identical score"
    )]
    pub(crate) fn update(&mut self, idx: u32, new_score: f64) {
        let old_score = self.score(idx);
        if old_score == new_score {
            return;
        }
        self.import(idx);
        self.score[widen(idx)] = new_score;
        self.tainted = true;
        if !self.contains(idx) {
            return;
        }
        if new_score > old_score {
            self.bubble_up(idx);
        } else {
            self.bubble_down(idx);
        }
    }

    pub(crate) fn compacted(&self, vars: u32, map: &[Option<u32>]) -> Heap {
        let mut heap = Heap::default();
        heap.enlarge(vars);
        if self.tainted {
            for (idx, &midx) in map.iter().enumerate() {
                if let Some(midx) = midx {
                    heap.update(midx, self.score[idx]);
                }
            }
        }
        for &idx in &self.stack {
            if let Some(midx) = map[widen(idx)] {
                heap.push(midx);
            }
        }
        heap
    }

    pub(crate) fn rescale(&mut self, factor: f64) {
        for score in &mut self.score {
            *score *= factor;
        }
    }

    fn bubble_up(&mut self, idx: u32) {
        let mut idx_pos = self.pos[widen(idx)];
        let idx_score = self.score[widen(idx)];
        while idx_pos > 0 {
            let parent_pos = (idx_pos - 1) / 2;
            let parent = self.stack[widen(parent_pos)];
            if self.score[widen(parent)] >= idx_score {
                break;
            }
            self.stack[widen(idx_pos)] = parent;
            self.pos[widen(parent)] = idx_pos;
            idx_pos = parent_pos;
        }
        self.stack[widen(idx_pos)] = idx;
        self.pos[widen(idx)] = idx_pos;
    }

    fn bubble_down(&mut self, idx: u32) {
        let end = narrow(self.stack.len());
        let mut idx_pos = self.pos[widen(idx)];
        let idx_score = self.score[widen(idx)];
        loop {
            let mut child_pos = 2 * idx_pos + 1;
            if child_pos >= end {
                break;
            }
            let mut child = self.stack[widen(child_pos)];
            let mut child_score = self.score[widen(child)];
            let sibling_pos = child_pos + 1;
            if sibling_pos < end {
                let sibling = self.stack[widen(sibling_pos)];
                let sibling_score = self.score[widen(sibling)];
                if sibling_score > child_score {
                    child = sibling;
                    child_pos = sibling_pos;
                    child_score = sibling_score;
                }
            }
            if child_score <= idx_score {
                break;
            }
            self.stack[widen(idx_pos)] = child;
            self.pos[widen(child)] = idx_pos;
            idx_pos = child_pos;
        }
        self.stack[widen(idx_pos)] = idx;
        self.pos[widen(idx)] = idx_pos;
    }
}
