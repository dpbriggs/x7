use std::collections::HashSet;

use im::Vector;
use itertools::Itertools;

use crate::{records::struct_record::StructRecord, symbols::Expr};

use super::RecordDoc;

#[derive(Default, Clone, PartialEq, Eq)]
pub(crate) struct SetRecord(HashSet<Expr>);

impl SetRecord {
    pub(crate) const RECORD_NAME: &'static str = "Set";

    // fn init(e: Vec<Expr>) -> Result<Self, String> {
    //     // TODO: Match behaviour
    // }

    fn contains(&self, e: Expr) -> bool {
        self.0.contains(&e)
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn display(&self) -> String {
        format!("{}<{{{}}}>", Self::RECORD_NAME, self.0.iter().join(" "))
    }

    fn to_list(&self) -> Vector<Expr> {
        self.0.iter().cloned().collect()
    }

    fn union(&self, other: &Self) -> Self {
        SetRecord(self.0.union(&other.0).cloned().collect())
    }

    fn intersection(&self, other: &Self) -> Self {
        SetRecord(self.0.intersection(&other.0).cloned().collect())
    }

    fn difference(&self, other: &Self) -> Self {
        SetRecord(self.0.difference(&other.0).cloned().collect())
    }

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(SetRecord::RECORD_NAME)
            .init_fn(&|e: Vec<Expr>, _| Ok(SetRecord(e.into_iter().collect())))
            .display_with(&SetRecord::display)
            .clone_with(&Clone::clone)
            .add_method("contains", SetRecord::contains)
            .add_method("union", SetRecord::union)
            .add_method("intersection", SetRecord::intersection)
            .add_method("difference", SetRecord::difference)
            .add_method("len", SetRecord::len)
            .add_method("to_list", SetRecord::to_list)
            .build()
    }
}

impl RecordDoc for SetRecord {
    fn name() -> &'static str {
        SetRecord::RECORD_NAME
    }

    fn type_doc() -> &'static str {
        "Basic Hash Set in x7.

;; Contains. Test whether an element exists in a Set. O(1) time.
;; Example:
(.contains (Set 0 1 2 3) 2)  ;; true
(.contains (Set 0 1 2 3) 10) ;; false

;; Union (creates new Set with elements from each)
;; Example:
(.union (Set 1 2 3)
        (Set 4 5 6)) ;; Set<{4, 5, 2, 6, 1, 3}>
(.union (apply Set (range 5)) (apply Set (range 5 10)))
;; Set<{5, 1, 7, 4, 3, 2, 8, 0, 9, 6}>

;; Intersection. Obtain the intersection of two Sets.
;; Example:
(.intersection (apply Set (range 10)) (apply Set (range 5 10)))
;; Set<{5, 6, 9, 7, 8}>

;; to_list. Convert the Set into a list. Order is undefined.
;; Example:
(.to_list (apply Set (range 5))) ;; (1 2 0 3 4)

;; len. Get the number of elements in a Set. Implements the \"len\" magic method.
;; Example:
(.len (Set '(0 1 2 3)))  ;; 4
(len (Set '())) ;; 0
"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[
            (
                "contains",
                "Test whether an element exists in a set. O(1) time.
Example:
(.contains (Set 0 1 2 3) 2)  ;; true
(.contains (Set 0 1 2 3) 10) ;; false",
            ),
            (
                "len",
                "Get the number of elements in a Set. Implements the \"len\" magic method.
Example:
(.len (Set 0 1 2 3))  ;; 4
(len (Set)) ;; 0",
            ),
            (
                "union",
                "Obtain the union of two Sets.
Example:
(.union (Set (range 5)) (Set (range 5 10)))
;; Set<{5, 1, 7, 4, 3, 2, 8, 0, 9, 6}>
",
            ),
            (
                "intersection",
                "Obtain the intersection of two Sets.
Example:
(.intersection (apply Set (range 10)) (apply Set (range 5 10)))
;; Set<{5, 6, 9, 7, 8}>",
            ),
            (
                "to_list",
                "Convert the Set into a list. Order is undefined.
Example:
(.to_list (apply Set (range 5))) ;; (1 2 0 3 4)
",
            ),
        ]
    }
}
