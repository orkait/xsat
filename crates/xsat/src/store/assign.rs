use crate::{
    solver::{idx, literal, Assigned, Frame, UNASSIGNED},
    store::convert::{narrow, widen},
};

#[derive(Debug)]
pub(crate) struct Assignment {
    pub(crate) values: Vec<i8>,
    pub(crate) assigned: Vec<Assigned>,
    pub(crate) trail: Vec<u32>,
    pub(crate) propagate: usize,
    pub(crate) frames: Vec<Frame>,
    pub(crate) level: u32,
    pub(crate) unassigned: u32,
    pub(crate) iterating: bool,
}

impl Default for Assignment {
    fn default() -> Assignment {
        Assignment {
            values: Vec::new(),
            assigned: Vec::new(),
            trail: Vec::new(),
            propagate: 0,
            frames: vec![Frame {
                decision: None,
                trail: 0,
                used: 0,
                promote: false,
            }],
            level: 0,
            unassigned: 0,
            iterating: false,
        }
    }
}

impl Assignment {
    pub(crate) fn unassign_above(
        &mut self,
        new_end: usize,
        new_level: u32,
        mut requeue: impl FnMut(u32),
    ) {
        let mut q = new_end;
        for p in new_end..self.trail.len() {
            let lit = self.trail[p];
            let idx = idx(lit);
            let assigned = &mut self.assigned[widen(idx)];
            if assigned.level <= new_level {
                assigned.trail = narrow(q);
                self.trail[q] = lit;
                q += 1;
            } else {
                if let Some(pair) = self
                    .values
                    .get_mut(widen(literal(idx))..)
                    .and_then(<[i8]>::first_chunk_mut::<2>)
                {
                    *pair = [UNASSIGNED; 2];
                }
                self.unassigned += 1;
                requeue(idx);
            }
        }
        self.trail.truncate(q);
    }
}
