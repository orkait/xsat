use crate::solver::Solver;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shown {
    Always,
    Nonzero,
    Verbose,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Counter {
    pub name: &'static str,
    pub value: u64,
    pub shown: Shown,
}

impl Counter {
    #[must_use]
    pub fn printed(self, verbose: Verbosity) -> bool {
        match (self.shown, verbose) {
            (Shown::Always, _) | (_, Verbosity::Complete) => true,
            (Shown::Nonzero, Verbosity::Brief) => self.value != 0,
            (Shown::Verbose, Verbosity::Brief) => false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verbosity {
    Brief,
    Complete,
}

impl Solver {
    #[must_use]
    pub fn counters(&self) -> Vec<Counter> {
        let statistics = &self.statistics;
        let units = u64::try_from(self.units.len()).unwrap_or(u64::MAX);
        [
            (
                "backbone_computations",
                statistics.backbone_computations,
                Shown::Verbose,
            ),
            ("clauses_binary", statistics.clauses_binary, Shown::Verbose),
            (
                "clauses_irredundant",
                statistics.clauses_irredundant,
                Shown::Verbose,
            ),
            (
                "clauses_redundant",
                statistics.clauses_redundant,
                Shown::Verbose,
            ),
            ("conflicts", statistics.conflicts, Shown::Always),
            ("decisions", statistics.decisions, Shown::Always),
            ("eliminations", statistics.eliminations, Shown::Verbose),
            ("probings", statistics.probings, Shown::Verbose),
            ("propagations", statistics.propagations, Shown::Always),
            ("reductions", statistics.reductions, Shown::Nonzero),
            ("reordered", statistics.reordered, Shown::Nonzero),
            ("rephased", statistics.rephased, Shown::Nonzero),
            ("restarts", statistics.restarts, Shown::Nonzero),
            ("search_ticks", statistics.search_ticks, Shown::Verbose),
            ("switched", statistics.switched, Shown::Always),
            ("units", units, Shown::Verbose),
            ("walks", statistics.walks, Shown::Nonzero),
        ]
        .into_iter()
        .map(|(name, value, shown)| Counter { name, value, shown })
        .collect()
    }
}
