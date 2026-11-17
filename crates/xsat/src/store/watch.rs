use crate::store::arena::Ref;

const BINARY: u32 = 1;
const LINES_SHIFT: u32 = 5;
const LINE_ROUND: usize = (1 << LINES_SHIFT) - 1;

pub(crate) type Watches = Vec<u32>;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Head {
    Binary(u32),
    Blocking(u32),
}

pub(crate) fn decode(word: u32) -> Head {
    let lit = word >> 1;
    if word & BINARY == 0 {
        Head::Blocking(lit)
    } else {
        Head::Binary(lit)
    }
}

pub(crate) fn blocking(lit: u32) -> u32 {
    lit << 1
}

pub(crate) fn binaries(watches: &[u32]) -> impl Iterator<Item = u32> + '_ {
    let mut p = 0;
    std::iter::from_fn(move || {
        while let Some(&head) = watches.get(p) {
            p += 1;
            match decode(head) {
                Head::Binary(other) => return Some(other),
                Head::Blocking(_) => p += 1,
            }
        }
        None
    })
}

pub(crate) fn large(at: Ref) -> u32 {
    at.0 << 1
}

pub(crate) fn large_ref(word: u32) -> Ref {
    Ref(word >> 1)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Occurrence {
    Binary(u32),
    Large(Ref),
}

pub(crate) fn occurrence(word: u32) -> Occurrence {
    match decode(word) {
        Head::Binary(other) => Occurrence::Binary(other),
        Head::Blocking(_) => Occurrence::Large(large_ref(word)),
    }
}

pub(crate) fn binary(other: u32) -> u32 {
    other << 1 | BINARY
}

pub(crate) fn push_binary(watches: &mut Watches, other: u32) {
    watches.push(binary(other));
}

pub(crate) fn push_blocking(watches: &mut Watches, blocking_lit: u32, at: Ref) {
    watches.extend([blocking(blocking_lit), at.0]);
}

pub(crate) fn remove_blocking(watches: &mut Watches, at: Ref) {
    let mut q = 0;
    let mut p = 0;
    while p < watches.len() {
        let head = watches[p];
        watches[q] = head;
        p += 1;
        q += 1;
        if let Head::Binary(_) = decode(head) {
            continue;
        }
        let tail = watches[p];
        watches[q] = tail;
        p += 1;
        q += 1;
        if tail == at.0 {
            q -= 2;
        }
    }
    watches.truncate(q);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Removal {
    First,
    All,
}

pub(crate) fn remove_binary(watches: &mut Watches, lit: u32, removal: Removal) {
    let mut removed = false;
    let (mut p, mut q) = (0, 0);
    while p < watches.len() {
        let head = watches[p];
        watches[q] = head;
        p += 1;
        q += 1;
        match decode(head) {
            Head::Binary(other) => {
                if other == lit && !(removed && removal == Removal::First) {
                    removed = true;
                    q -= 1;
                }
            }
            Head::Blocking(_) => {
                watches[q] = watches[p];
                p += 1;
                q += 1;
            }
        }
    }
    watches.truncate(q);
}

pub(crate) fn cache_lines(words: usize) -> u64 {
    u64::try_from((words + LINE_ROUND) >> LINES_SHIFT).unwrap_or(u64::MAX)
}
