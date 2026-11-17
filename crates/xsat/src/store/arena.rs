use crate::store::convert::{narrow, widen};

const FLAGS: usize = 0;
const SEARCHED: usize = 1;
const SIZE: usize = 2;
const HEADER: usize = 3;
const WARD: usize = 4;
const LD_MAX_REF: u32 = 31;
const MAX_REF: usize = 1 << LD_MAX_REF;
const GLUE_BITS: u32 = 19;
const MAX_GLUE: u32 = (1 << GLUE_BITS) - 1;
const GARBAGE: u32 = 1 << GLUE_BITS;
const REDUNDANT: u32 = GARBAGE << 1;
const REASON: u32 = REDUNDANT << 1;
const USED_SHIFT: u32 = GLUE_BITS + 3;
const USED_BITS: u32 = 5;
pub(crate) const MAX_USED: u32 = (1 << USED_BITS) - 1;
const USED_MASK: u32 = MAX_USED << USED_SHIFT;
const SHRUNKEN: u32 = 1 << (USED_SHIFT + USED_BITS);
const VIVIFY: u32 = SHRUNKEN << 1;
const QUOTIENT: u32 = VIVIFY << 1;
const SUBSUME: u32 = QUOTIENT << 1;
const SWEPT: u32 = SUBSUME << 1;
pub(crate) const INITIAL_SEARCHED: u32 = 2;
pub(crate) const INVALID_LIT: u32 = u32::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Kind {
    Irredundant,
    Redundant,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Ref(pub(crate) u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Vivify {
    Prioritized,
    Normal,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Arena {
    words: Vec<u32>,
}

impl Arena {
    #[expect(
        clippy::expect_used,
        reason = "references count 16-byte wards in 31 bits, as in Kissat; running out is a resource limit, fatal there too"
    )]
    pub(crate) fn allocate(&mut self, kind: Kind, glue: u32, lits: &[u32]) -> Ref {
        let first = self.words.len() / WARD;
        let last = first + (HEADER + lits.len()).div_ceil(WARD);
        let at = u32::try_from(first)
            .ok()
            .filter(|_| last <= MAX_REF)
            .map(Ref)
            .expect("maximum arena capacity of 2^31 16-byte words exhausted");
        let flags = glue.min(MAX_GLUE)
            | match kind {
                Kind::Irredundant => 0,
                Kind::Redundant => REDUNDANT,
            };
        self.words
            .extend([flags, INITIAL_SEARCHED, narrow(lits.len())]);
        self.words.extend_from_slice(lits);
        self.words.resize(last * WARD, INVALID_LIT);
        at
    }

    fn base(at: Ref) -> usize {
        widen(at.0) * WARD
    }

    fn start(at: Ref) -> usize {
        Arena::base(at) + HEADER
    }

    fn flags(&self, at: Ref) -> u32 {
        self.words[Arena::base(at) + FLAGS]
    }

    pub(crate) fn end(&self) -> Ref {
        Ref(narrow(self.words.len() / WARD))
    }

    pub(crate) fn next(&self, at: Ref) -> Ref {
        let mut end = Arena::start(at) + widen(self.size(at));
        if self.flags(at) & SHRUNKEN != 0 {
            while self.words[end] != INVALID_LIT {
                end += 1;
            }
            end += 1;
        }
        Ref(narrow(end.div_ceil(WARD)))
    }

    pub(crate) fn size(&self, at: Ref) -> u32 {
        self.words[Arena::base(at) + SIZE]
    }

    pub(crate) fn set_size(&mut self, at: Ref, size: u32) {
        self.words[Arena::base(at) + SIZE] = size;
        self.words[Arena::base(at) + FLAGS] &= !SHRUNKEN;
    }

    pub(crate) fn shrink(&mut self, at: Ref, size: u32) {
        if self.flags(at) & SHRUNKEN == 0 {
            let old_end = Arena::start(at) + widen(self.size(at)) - 1;
            self.words[old_end] = INVALID_LIT;
            self.words[Arena::base(at) + FLAGS] |= SHRUNKEN;
        }
        self.words[Arena::base(at) + SIZE] = size;
    }

    pub(crate) fn move_clause(&mut self, src: Ref, dst: Ref) {
        let end = Arena::start(src) + widen(self.size(src));
        self.words
            .copy_within(Arena::base(src)..end, Arena::base(dst));
        self.words[Arena::base(dst) + FLAGS] &= !SHRUNKEN;
    }

    pub(crate) fn subsume(&self, at: Ref) -> bool {
        self.flags(at) & SUBSUME != 0
    }

    pub(crate) fn set_subsume(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] |= SUBSUME;
    }

    pub(crate) fn clear_subsume(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] &= !SUBSUME;
    }

    pub(crate) fn swept(&self, at: Ref) -> bool {
        self.flags(at) & SWEPT != 0
    }

    pub(crate) fn set_swept(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] |= SWEPT;
    }

    pub(crate) fn clear_swept(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] &= !SWEPT;
    }

    pub(crate) fn lits(&self, at: Ref) -> &[u32] {
        let start = Arena::start(at);
        &self.words[start..start + widen(self.size(at))]
    }

    pub(crate) fn lits_mut(&mut self, at: Ref) -> &mut [u32] {
        let start = Arena::start(at);
        let end = start + widen(self.size(at));
        &mut self.words[start..end]
    }

    pub(crate) fn lit(&self, at: Ref, position: u32) -> u32 {
        self.words[Arena::start(at) + widen(position)]
    }

    pub(crate) fn set_lit(&mut self, at: Ref, position: u32, lit: u32) {
        self.words[Arena::start(at) + widen(position)] = lit;
    }

    pub(crate) fn copy_flags(&mut self, src: Ref, dst: Ref) {
        self.words[Arena::base(dst) + FLAGS] = self.flags(src);
    }

    pub(crate) fn move_redundant_to_end(&mut self, start: Ref) {
        let mut irredundant = Vec::new();
        let mut redundant = Vec::new();
        let mut at = start;
        while at < self.end() {
            let next = self.next(at);
            let words = &self.words[Arena::base(at)..Arena::base(next)];
            if self.redundant(at) {
                redundant.extend_from_slice(words);
            } else {
                irredundant.extend_from_slice(words);
            }
            at = next;
        }
        self.truncate(start);
        self.words.append(&mut irredundant);
        self.words.append(&mut redundant);
    }

    pub(crate) fn truncate(&mut self, end: Ref) {
        self.words.truncate(Arena::base(end));
    }

    pub(crate) fn set_searched(&mut self, at: Ref, position: u32) {
        self.words[Arena::base(at) + SEARCHED] = position;
    }

    pub(crate) fn glue(&self, at: Ref) -> u32 {
        self.flags(at) & MAX_GLUE
    }

    pub(crate) fn set_glue(&mut self, at: Ref, glue: u32) {
        let word = &mut self.words[Arena::base(at) + FLAGS];
        *word = (*word & !MAX_GLUE) | glue.min(MAX_GLUE);
    }

    pub(crate) fn used(&self, at: Ref) -> u32 {
        (self.flags(at) & USED_MASK) >> USED_SHIFT
    }

    pub(crate) fn set_used(&mut self, at: Ref, used: u32) {
        let word = &mut self.words[Arena::base(at) + FLAGS];
        *word = (*word & !USED_MASK) | (used.min(MAX_USED) << USED_SHIFT);
    }

    pub(crate) fn garbage(&self, at: Ref) -> bool {
        self.flags(at) & GARBAGE != 0
    }

    pub(crate) fn set_garbage(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] |= GARBAGE;
    }

    pub(crate) fn redundant(&self, at: Ref) -> bool {
        self.flags(at) & REDUNDANT != 0
    }

    pub(crate) fn quotient(&self, at: Ref) -> bool {
        self.flags(at) & QUOTIENT != 0
    }

    pub(crate) fn mark_quotient(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] |= QUOTIENT;
    }

    pub(crate) fn unmark_quotient(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] &= !QUOTIENT;
    }

    pub(crate) fn vivify(&self, at: Ref) -> Vivify {
        if self.flags(at) & VIVIFY == 0 {
            Vivify::Normal
        } else {
            Vivify::Prioritized
        }
    }

    pub(crate) fn set_vivify(&mut self, at: Ref, vivify: Vivify) {
        let word = &mut self.words[Arena::base(at) + FLAGS];
        match vivify {
            Vivify::Prioritized => *word |= VIVIFY,
            Vivify::Normal => *word &= !VIVIFY,
        }
    }

    pub(crate) fn set_irredundant(&mut self, at: Ref) {
        self.words[Arena::base(at) + FLAGS] &= !REDUNDANT;
    }

    pub(crate) fn reason(&self, at: Ref) -> bool {
        self.flags(at) & REASON != 0
    }

    pub(crate) fn set_reason(&mut self, at: Ref, reason: Reason) {
        let word = &mut self.words[Arena::base(at) + FLAGS];
        match reason {
            Reason::Marked => *word |= REASON,
            Reason::Unmarked => *word &= !REASON,
        }
    }

    pub(crate) fn refs(&self) -> impl Iterator<Item = Ref> + '_ {
        let mut at = Ref(0);
        std::iter::from_fn(move || {
            let found = at;
            (found < self.end()).then(|| {
                at = self.next(found);
                found
            })
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Reason {
    Marked,
    Unmarked,
}

pub(crate) struct Watched<'a> {
    pub(crate) garbage: bool,
    pub(crate) searched: &'a mut u32,
    pub(crate) lits: &'a mut [u32],
}

impl Arena {
    pub(crate) fn watched(&mut self, at: Ref) -> Option<Watched<'_>> {
        let ([flags, searched, size], rest) = self
            .words
            .get_mut(Arena::base(at)..)?
            .split_first_chunk_mut::<HEADER>()?;
        Some(Watched {
            garbage: *flags & GARBAGE != 0,
            searched,
            lits: rest.get_mut(..widen(*size))?,
        })
    }
}
