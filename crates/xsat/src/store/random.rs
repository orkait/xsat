use crate::store::convert::truncate;

const MULTIPLIER: u64 = 6_364_136_223_846_793_005;
const INCREMENT: u64 = 1_442_695_040_888_963_407;
const HIGH_HALF: u32 = 32;
const SCALE: f64 = 4_294_967_296.0;

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Generator(pub(crate) u64);

impl Generator {
    pub(crate) fn next64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT);
        self.0
    }

    pub(crate) fn next32(&mut self) -> u32 {
        u32::try_from(self.next64() >> HIGH_HALF).unwrap_or(u32::MAX)
    }

    pub(crate) fn pick(&mut self, low: u32, high: u32) -> u32 {
        if low == high {
            return low;
        }
        let scaled = f64::from(high - low) * self.pick_double();
        low + u32::try_from(truncate(scaled)).unwrap_or(0)
    }

    pub(crate) fn pick_double(&mut self) -> f64 {
        f64::from(self.next32()) / SCALE
    }
}
