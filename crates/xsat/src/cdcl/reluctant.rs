#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Reluctant {
    limited: bool,
    trigger: bool,
    period: u64,
    wait: u64,
    u: u64,
    v: u64,
    limit: u64,
}

impl Reluctant {
    pub(crate) fn enable(&mut self, period: u64, limit: u64) {
        let period = if limit > 0 && period > limit {
            limit
        } else {
            period
        };
        *self = Reluctant {
            limited: limit > 0,
            trigger: false,
            period,
            wait: period,
            u: 1,
            v: 1,
            limit,
        };
    }

    pub(crate) fn disable(&mut self) {
        self.period = 0;
    }

    pub(crate) fn tick(&mut self) {
        if self.period == 0 || self.trigger {
            return;
        }
        self.wait -= 1;
        if self.wait > 0 {
            return;
        }
        let (mut u, mut v) = (self.u, self.v);
        if u & u.wrapping_neg() == v {
            u += 1;
            v = 1;
        } else {
            v *= 2;
        }
        let mut wait = v * self.period;
        if self.limited && wait > self.limit {
            u = 1;
            v = 1;
            wait = self.period;
        }
        self.trigger = true;
        self.wait = wait;
        self.u = u;
        self.v = v;
    }

    pub(crate) fn triggered(&mut self) -> bool {
        if !self.trigger {
            return false;
        }
        self.trigger = false;
        true
    }
}
