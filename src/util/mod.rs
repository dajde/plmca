//! Utility functions.
pub mod parse;

use std::{collections::HashMap, hash::Hash};

/// Create an `n` time cartesian power of `input`.
pub fn cartesian_power<'a, T, I>(input: &'a I, n: usize) -> Vec<Vec<&'a T>>
where
    &'a I: IntoIterator<Item = &'a T>,
{
    if n == 0 {
        return Vec::new();
    }
    if n == 1 {
        return input.into_iter().map(|x| vec![x]).collect();
    }

    let mut combinations = Vec::new();
    let rest = cartesian_power(input, n - 1);

    for item in input.into_iter() {
        for r in &rest {
            let mut combination = vec![item];
            combination.extend(r);
            combinations.push(combination);
        }
    }

    combinations
}

/// A data structure which stores objects together with their unique ids.
#[derive(Clone, Default, Debug)]
pub struct IdMap<K, V> {
    map: HashMap<K, V>,
}

impl<K: Eq + Hash + Default, V: Copy + Default + Eq + From<usize>> IdMap<K, V> {
    /// Create an empty `IdMap`.
    pub fn new() -> IdMap<K, V> {
        Self::default()
    }

    /// Insert a new object with a unique ID.
    ///
    /// Returns the ID.
    ///
    /// If this object already exists, just return its ID.
    pub fn insert(&mut self, obj: K) -> V {
        if let Some(&id) = self.map.get(&obj) {
            id
        } else {
            let new_id = V::from(self.map.len());
            self.map.insert(obj, new_id);

            new_id
        }
    }

    /// Get the id corresponding to object.
    pub fn id(&self, obj: &K) -> Option<V> {
        self.map.get(obj).copied()
    }

    /// Get all ids stored in this `IdMap`.
    pub fn ids(&self) -> Vec<V> {
        self.map.values().copied().collect()
    }

    /// Get object corresponding to `id`, or `None` if it is not present.
    pub fn object(&self, id: V) -> Option<&K> {
        self.map.iter().find(|x| *x.1 == id).map(|x| x.0)
    }

    /// Check whether an object is already in the `IdMap`.
    pub fn contains(&self, obj: &K) -> bool {
        self.map.contains_key(obj)
    }
}
