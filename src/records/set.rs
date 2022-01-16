use im::{vector, Vector};
use itertools::Itertools;

use crate::records::{Record, RecordDoc, RecordType};
use crate::symbols::{Expr, LispResult, SymbolTable};
use crate::{bad_types, exact_len, record, try_call_method, unknown_method};
use anyhow::{anyhow, Context};
use std::collections::HashSet;
use std::sync::Arc;

#[derive(Clone)]
pub(crate) struct SetRecord {
    coll: Arc<HashSet<Expr>>,
    id: u64,
}

impl SetRecord {
    pub(crate) fn from_x7(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        let items = if let Ok(l) = exprs[0].get_list() {
            l
        } else if let Ok(i) = exprs[0].get_iterator() {
            i.eval(symbol_table)?.get_list()?
        } else {
            return bad_types!("list or iterator", &exprs[0]);
        };
        let set = SetRecord {
            coll: Arc::new(items.into_iter().collect()),
            id: rand::random(),
        };
        record!(set)
    }

    fn contains(&self, exprs: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        Ok(Expr::Bool(self.coll.contains(&exprs[0])))
    }

    fn union(&self, exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        let rec = exprs[0].get_record()?;
        if rec.type_name() != self.type_name() {
            return bad_types!("set", rec);
        }
        let list = rec
            .call_method("to_list", vector![], symbol_table)?
            .get_list()?;
        record!(SetRecord {
            coll: Arc::new(self.coll.iter().chain(list.iter()).cloned().collect()),
            id: rand::random()
        })
    }

    fn intersection(&self, exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        let rec = exprs[0].get_record()?;
        if rec.type_name() != self.type_name() {
            return bad_types!("set", rec);
        }
        let list = rec
            .call_method("to_list", vector![], symbol_table)?
            .get_list()?;
        let mut new_coll = HashSet::new();
        for item in list.into_iter() {
            if self.coll.contains(&item) {
                new_coll.insert(item);
            }
        }
        record!(SetRecord {
            coll: Arc::new(new_coll),
            id: rand::random()
        })
    }

    fn to_list(&self, exprs: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(exprs, 0);
        Ok(Expr::List(self.coll.iter().cloned().collect()))
    }

    pub fn len(&self, exprs: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(exprs, 0);
        Ok(Expr::num(self.coll.len()))
    }
}

impl Record for SetRecord {
    fn call_method(
        &self,
        sym: &str,
        args: im::Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        match sym {
            "union" => self.union(args, symbol_table),
            "intersection" => self.intersection(args, symbol_table),
            sym => try_call_method!(self, sym, args, contains, to_list, len),
        }
    }

    fn display(&self) -> String {
        let max_shown = 20;
        let needs_ellipses = self.coll.len() > max_shown;
        let mut s = String::from("Set<{");
        s += &self.coll.iter().take(max_shown).join(", ");
        if needs_ellipses {
            s += &format!(", ... {} elided ...", self.coll.len() - max_shown);
        }
        s += "}>";
        s
    }

    fn debug(&self) -> String {
        self.display()
    }

    fn clone(&self) -> RecordType {
        Box::new(Clone::clone(self))
    }

    fn methods(&self) -> Vec<String> {
        SetRecord::method_doc()
            .iter()
            .map(|(l, _)| l.to_string())
            .collect()
    }

    fn type_name(&self) -> String {
        "SetRecord".to_string()
    }

    fn id(&self) -> u64 {
        self.id
    }
}

impl RecordDoc for SetRecord {
    fn name() -> &'static str {
        "SetRecord"
    }

    fn type_doc() -> &'static str {
        "Basic Hash Set in x7.

;; Contains. Test whether an element exists in a set. O(1) time.
;; Example:
(.contains (set '(0 1 2 3)) 2)  ;; true
(.contains (set '(0 1 2 3)) 10) ;; false

;; Union (creates new set with elements from each)
;; Example:
(.union (set '(1 2 3))
        (set '(4 5 6))) ;; Set<{4, 5, 2, 6, 1, 3}>
(.union (set (lazy (range 5))) (set (range 5 10)))
;; Set<{5, 1, 7, 4, 3, 2, 8, 0, 9, 6}>

;; Intersection. Obtain the intersection of two sets.
;; Example:
(.intersection (set (range 10)) (set (range 5 10)))
;; Set<{5, 6, 9, 7, 8}>

;; to_list. Convert the set into a list. Order is undefined.
;; Example:
(.to_list (set (range 5))) ;; (1 2 0 3 4)

;; len. Get the number of elements in a set. Implements the \"len\" magic method.
;; Example:
(.len (set '(0 1 2 3)))  ;; 4
(len (set '())) ;; 0
"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[
            (
                "contains",
                "Test whether an element exists in a set. O(1) time.
Example:
(.contains (set '(0 1 2 3)) 2)  ;; true
(.contains (set '(0 1 2 3)) 10) ;; false",
            ),
            (
                "len",
                "Get the number of elements in a set. Implements the \"len\" magic method.
Example:
(.len (set '(0 1 2 3)))  ;; 4
(len (set '())) ;; 0",
            ),
            (
                "union",
                "Obtain the union of two sets.
Example:
(.union (set (lazy (range 5))) (set (range 5 10)))
;; Set<{5, 1, 7, 4, 3, 2, 8, 0, 9, 6}>
",
            ),
            (
                "intersection",
                "Obtain the intersection of two sets.
Example:
(.intersection (set (range 10)) (set (range 5 10)))
;; Set<{5, 6, 9, 7, 8}>",
            ),
            (
                "to_list",
                "Convert the set into a list. Order is undefined.
Example:
(.to_list (set (range 5))) ;; (1 2 0 3 4)
",
            ),
        ]
    }
}
