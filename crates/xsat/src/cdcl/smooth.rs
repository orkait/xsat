#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Smooth {
    pub(crate) value: f64,
    biased: f64,
    alpha: f64,
    beta: f64,
    exp: f64,
}

impl Smooth {
    fn new(window: i32) -> Smooth {
        let alpha = 1.0 / f64::from(window);
        Smooth {
            value: 0.0,
            biased: 0.0,
            alpha,
            beta: 1.0 - alpha,
            exp: 1.0,
        }
    }

    #[expect(
        clippy::float_cmp,
        reason = "Kissat stops bias correction once the exponent no longer changes"
    )]
    pub(crate) fn update(&mut self, y: f64) {
        let delta = y - self.biased;
        let scaled_delta = self.alpha * delta;
        let new_biased = self.biased + scaled_delta;
        self.biased = new_biased;
        if self.exp == 0.0 {
            self.value = new_biased;
            return;
        }
        let new_exp = self.exp * self.beta;
        if new_exp == self.exp {
            self.exp = 0.0;
            self.value = new_biased;
        } else {
            self.exp = new_exp;
            self.value = new_biased / (1.0 - new_exp);
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Averages {
    initialized: bool,
    pub(crate) fast_glue: Smooth,
    pub(crate) slow_glue: Smooth,
    pub(crate) decision_rate: Smooth,
    pub(crate) saved_decisions: u64,
}

impl Averages {
    pub(crate) fn init(&mut self, slow: i32, fast: i32) {
        if self.initialized {
            return;
        }
        self.fast_glue = Smooth::new(fast);
        self.slow_glue = Smooth::new(slow);
        self.decision_rate = Smooth::new(slow);
        self.initialized = true;
    }
}
