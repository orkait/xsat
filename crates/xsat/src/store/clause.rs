use crate::{
    inprocess::backbone::{Order, Watching},
    store::{
        arena::{Arena, Ref},
        watch::Watches,
    },
};

const LAST_LEARNED: usize = 4;

#[derive(Debug)]
pub(crate) struct Clauses {
    pub(crate) arena: Arena,
    pub(crate) watches: Vec<Watches>,
    pub(crate) last_irredundant: Option<Ref>,
    pub(crate) first_reducible: Option<Ref>,
    pub(crate) last_learned: [Option<Ref>; LAST_LEARNED],
    pub(crate) watching: Watching,
    pub(crate) order: Order,
}

impl Default for Clauses {
    fn default() -> Clauses {
        Clauses {
            arena: Arena::default(),
            watches: Vec::new(),
            last_irredundant: None,
            first_reducible: None,
            last_learned: [None; LAST_LEARNED],
            watching: Watching::Sparse,
            order: Order::Mixed,
        }
    }
}
