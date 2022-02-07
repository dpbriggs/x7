use std::collections::HashMap;

use im::Vector;
use itertools::Itertools;

use crate::symbols::{Expr, LispResult};

use super::{struct_record::StructRecord, RecordDoc};

#[derive(Default, Clone, Debug, PartialEq)]
pub(crate) struct DictRecord(HashMap<Expr, Expr>);

impl DictRecord {
    pub(crate) const RECORD_NAME: &'static str = "Dict";

    fn init(items: Vec<Expr>) -> LispResult<Self> {
        anyhow::ensure!(
            items.len() % 2 == 0,
            "Dict requires an even list of arguments! Was given {:?}",
            &items
        );
        Ok(DictRecord(items.into_iter().tuples().collect()))
    }

    fn display(&self) -> String {
        format!(
            "{}<{{{}}}>",
            Self::RECORD_NAME,
            self.0.iter().map(|(k, v)| format!("{}:{}", k, v)).join(" ")
        )
    }

    fn assoc(&self, other: Vec<Expr>) -> LispResult<Self> {
        anyhow::ensure!(
            other.len() % 2 == 0,
            "Dict requires an even list of arguments! Was given {:?}",
            &other
        );
        let mut hashmap = self.0.clone();
        for (k, v) in other.into_iter().tuples() {
            hashmap.insert(k, v);
        }
        Ok(DictRecord(hashmap))
    }

    fn get(&self, key: Expr) -> Option<Expr> {
        self.0.get(&key).cloned()
    }

    fn contains(&self, key: Expr) -> bool {
        self.0.contains_key(&key)
    }

    fn merge(&self, other: &Self) -> Self {
        DictRecord(
            self.0
                .iter()
                .chain(&other.0)
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        )
    }

    fn merge_mut(&mut self, other: &Self) {
        self.0
            .extend(other.0.iter().map(|(k, v)| (k.clone(), v.clone())));
    }

    fn remove(&self, key: Expr) -> LispResult<Self> {
        let mut hashmap = self.0.clone();
        hashmap.remove(&key);
        Ok(DictRecord(hashmap))
    }

    fn keys(&self) -> Vector<Expr> {
        self.0.keys().cloned().collect()
    }

    fn values(&self) -> Vector<Expr> {
        self.0.values().cloned().collect()
    }

    fn update(&mut self, key: Expr, value: Expr) -> Option<Expr> {
        self.0.insert(key, value)
    }

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(DictRecord::RECORD_NAME)
            .init_fn(&DictRecord::init)
            .clone_with(&Clone::clone) // Just clone it always as we're immutable
            .display_with(&DictRecord::display)
            .add_method("keys", DictRecord::keys)
            .add_method("values", DictRecord::values)
            .add_method("get", DictRecord::get)
            .add_method("contains", DictRecord::contains)
            .add_method("merge", DictRecord::merge)
            .add_method("set", DictRecord::assoc)
            .add_method("assoc", DictRecord::assoc)
            .add_method("remove", DictRecord::remove)
            .build()
    }
}

impl RecordDoc for DictRecord {
    fn name() -> &'static str {
        DictRecord::RECORD_NAME
    }

    fn type_doc() -> &'static str {
        "Immutable dictionary.
Example:
(dict \"a\" 1 \"b\" 2) ;
"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[]
    }
}

pub(crate) struct DictMutRecord;

impl DictMutRecord {
    pub(crate) const RECORD_NAME: &'static str = "DictMut";

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(DictMutRecord::RECORD_NAME)
            .init_fn(&DictRecord::init)
            .display_with(&DictRecord::display)
            .add_method("keys", DictRecord::keys)
            .add_method("values", DictRecord::values)
            .add_method("get", DictRecord::get)
            .add_method("contains", DictRecord::contains)
            .add_method("assoc", DictRecord::assoc)
            .add_method("remove", DictRecord::remove)
            .add_method_mut("merge", DictRecord::merge_mut)
            .add_method_mut("update", DictRecord::update)
            .build()
    }
}

impl RecordDoc for DictMutRecord {
    fn name() -> &'static str {
        DictMutRecord::RECORD_NAME
    }

    fn type_doc() -> &'static str {
        "Mutable dictionary type"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[("Docs", "TBD")]
    }
}
