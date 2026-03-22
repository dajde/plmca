//! Utility functions.

pub mod parse;

/// Create an `n` time cartesian power of `input`.
pub fn cartesian_power<T>(input: &Vec<T>, n: usize) -> Vec<Vec<&T>> {
    if n == 0 {
        return Vec::new();
    }
    if n == 1 {
        return input.iter().map(|x| vec![x]).collect();
    }

    let mut combinations = Vec::new();
    let rest = cartesian_power(input, n - 1);

    for item in input {
        for r in &rest {
            let mut combination = vec![item];
            combination.extend(r);
            combinations.push(combination);
        }
    }

    combinations
}

use std::{collections::HashMap, hash::Hash};

/// A data structure which stores objects together with their unique ids.
#[derive(Clone)]
pub struct IdMap<T> {
    map: HashMap<T, usize>,
}

impl<T: Eq + Hash> IdMap<T> {
    /// Create an empty `IdMap`.
    pub fn new() -> IdMap<T> {
        Self {
            map: HashMap::new(),
        }
    }

    /// Insert a new object with a unique ID.
    ///
    /// Returns the ID.
    ///
    /// If this object already exists, just return its ID.
    pub fn insert(&mut self, obj: T) -> usize {
        if let Some(&id) = self.map.get(&obj) {
            id
        } else {
            let new_id = self.map.len();
            self.map.insert(obj, new_id);

            new_id
        }
    }

    /// Get the id corresponding to object.
    pub fn id(&self, obj: &T) -> Option<usize> {
        self.map.get(obj).copied()
    }

    /// Get all ids stored in this `IdMap`.
    pub fn ids(&self) -> Vec<usize> {
        self.map.values().copied().collect()
    }

    /// Get object corresponding to `id`, or `None` if it is not present.
    pub fn object(&self, id: usize) -> Option<&T> {
        self.map.iter().find(|x| *x.1 == id).map(|x| x.0)
    }
}
