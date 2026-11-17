use crate::{
    solver::{idx, negated, Solver},
    store::convert::{narrow, widen},
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Flag {
    Backbone0,
    Backbone1,
    Eliminate,
    Eliminated,
    Factor0,
    Factor1,
    Fixed,
    Subsume,
    Sweep,
}

impl Flag {
    const fn bit(self) -> u16 {
        match self {
            Flag::Backbone0 => 1,
            Flag::Backbone1 => 2,
            Flag::Eliminate => 4,
            Flag::Eliminated => 8,
            Flag::Factor0 => 16,
            Flag::Factor1 => 32,
            Flag::Fixed => 64,
            Flag::Subsume => 128,
            Flag::Sweep => 256,
        }
    }

    pub(crate) fn of(lit: u32, positive: Flag, negative: Flag) -> Flag {
        if negated(lit) {
            negative
        } else {
            positive
        }
    }
}

impl Solver {
    pub(crate) fn mark_removed_literal(&mut self, lit: u32) {
        let flags = &mut self.flags[widen(idx(lit))];
        if flags.has(Flag::Fixed) || flags.has(Flag::Eliminate) {
            return;
        }
        flags.set(Flag::Eliminate);
        self.statistics.variables_eliminate += 1;
    }

    pub(crate) fn mark_added_literal(&mut self, lit: u32) {
        let flags = &mut self.flags[widen(idx(lit))];
        if !flags.has(Flag::Subsume) {
            flags.set(Flag::Subsume);
            self.statistics.variables_subsume += 1;
        }
        let flag = Flag::of(lit, Flag::Factor0, Flag::Factor1);
        if !flags.has(flag) {
            flags.set(flag);
            self.statistics.literals_factor += 1;
        }
    }

    pub(crate) fn mark_eliminated_variable(&mut self, idx: u32) {
        self.flags[widen(idx)].set(Flag::Eliminated);
        self.deactivate_variable(idx);
        let eidx = widen(self.exports[widen(idx)]);
        self.imports[eidx] = None;
        if self.eliminated_at.len() <= eidx {
            self.eliminated_at.resize(eidx + 1, None);
        }
        self.eliminated_at[eidx] = Some(narrow(self.eliminated.len()));
        self.eliminated.push(0);
        self.assignment.unassigned -= 1;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) struct Flags(u16);

impl Flags {
    pub(crate) const fn has(self, flag: Flag) -> bool {
        self.0 & flag.bit() != 0
    }

    pub(crate) fn set(&mut self, flag: Flag) {
        self.0 |= flag.bit();
    }

    pub(crate) fn clear(&mut self, flag: Flag) {
        self.0 &= !flag.bit();
    }
}
