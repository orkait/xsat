const GOLDEN_GAMMA: u64 = 0x9e37_79b9_7f4a_7c15;
const MIX_FIRST: u64 = 0xbf58_476d_1ce4_e5b9;
const MIX_SECOND: u64 = 0x94d0_49bb_1331_11eb;
const SHIFT_FIRST: u32 = 30;
const SHIFT_SECOND: u32 = 27;
const SHIFT_LAST: u32 = 31;

#[derive(Debug)]
pub(crate) struct Random(u64);

impl Random {
    pub(crate) fn new(seed: u64) -> Random {
        Random(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(GOLDEN_GAMMA);
        let mut mixed = self.0;
        mixed = (mixed ^ (mixed >> SHIFT_FIRST)).wrapping_mul(MIX_FIRST);
        mixed = (mixed ^ (mixed >> SHIFT_SECOND)).wrapping_mul(MIX_SECOND);
        mixed ^ (mixed >> SHIFT_LAST)
    }

    fn below(&mut self, bound: u64) -> u64 {
        if bound == 0 {
            return 0;
        }
        let zone = u64::MAX - u64::MAX % bound;
        loop {
            let drawn = self.next();
            if drawn < zone {
                return drawn % bound;
            }
        }
    }

    pub(crate) fn randrange(&mut self, start: i64, stop: i64) -> i64 {
        start.saturating_add_unsigned(self.below(stop.abs_diff(start)))
    }

    fn upto(&mut self, stop: usize) -> usize {
        let drawn = self.below(u64::try_from(stop).unwrap_or(u64::MAX));
        usize::try_from(drawn).unwrap_or_default()
    }

    pub(crate) fn pick<T, const K: usize>(&mut self, options: [T; K]) -> T {
        const { assert!(K > 0, "a choice needs at least one option") };
        let at = self.upto(K);
        Vec::from(options).swap_remove(at)
    }

    pub(crate) fn pick_from<T: Clone>(&mut self, options: &[T]) -> Option<T> {
        if options.is_empty() {
            return None;
        }
        let at = self.upto(options.len());
        options.get(at).cloned()
    }
}
