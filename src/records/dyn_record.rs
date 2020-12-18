use crate::records::Record;
use crate::symbols::{Expr, Function, LispResult, Symbol, SymbolTable};
use crate::{record, unknown_method};
use anyhow::anyhow;
use anyhow::bail;
use dashmap::DashMap;
use im::Vector;
use itertools::Itertools;
use std::sync::Arc;

#[derive(Default, Debug, Clone)]
pub struct DynRecord {
    name: Symbol,
    doc: Option<String>,
    fields: DashMap<Symbol, Expr>,
    initialized: bool,
    fields_order: Vec<Symbol>,
    methods: Arc<DashMap<Symbol, Function>>,
}

impl Record for DynRecord {
    fn call_method(
        &self,
        sym: &str,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        self.call_method(sym, args, symbol_table)
    }

    fn display(&self) -> String {
        if self.initialized {
            format!(
                "Record<{}, fields=[ {} ]>",
                self.name,
                self.fields_order
                    .iter()
                    .map(|v| format!("{}: {}", v, &*self.fields.get(v).unwrap()))
                    .join(" ")
            )
        } else {
            format!("Record<{}, uninitialized>", self.name)
        }
    }

    fn debug(&self) -> String {
        self.display()
    }

    fn clone(&self) -> super::RecordType {
        Box::new(Clone::clone(self))
    }

    fn methods(&self) -> Vec<String> {
        self.methods.iter().map(|m| m.key().to_string()).collect()
    }

    fn type_name(&self) -> String {
        self.name.clone()
    }

    fn call_as_fn(&self, args: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        if args.len() != self.fields_order.len() {
            bail!(
                "{} requires {} fields [ {} ], but only received {} arguments",
                self.display(),
                self.fields_order.len(),
                self.fields_order.iter().join(" "),
                args.len()
            )
        }
        let fields = DashMap::new();
        let fields_value_iter = self.fields_order.iter().cloned().zip(args.iter().cloned());
        for (field, value) in fields_value_iter {
            fields.insert(field, value.eval(symbol_table)?);
        }
        let rec = DynRecord {
            fields,
            initialized: true,
            ..Clone::clone(self)
        };
        record!(rec)
    }

    fn defmethod(&self, args: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        self.add_method_x7(args, symbol_table)
    }
}

// (defrecord rec-name "optional-doc" field1 field2 field3)
// Adds rec-name to symbol table
// (.defmethod rec-name method-name
//   "optional doc"
//   (arg1)
//   ;; body
//   (+ arg1 field1 field2 field3)) ;; fields are added to the symbol table

impl DynRecord {
    pub fn defrecord(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        let name = exprs[0].get_symbol_string()?;
        let mut skip_to_fields = 1;
        let doc = if let Ok(s) = exprs[1].get_string() {
            skip_to_fields += 1;
            symbol_table.add_doc_item(name.clone(), s.clone());
            Some(s)
        } else {
            None
        };
        let fields_order = exprs
            .iter()
            .skip(skip_to_fields)
            .map(|e| e.get_symbol_string())
            .try_collect()?;
        let rec = DynRecord {
            name,
            doc,
            fields_order,
            initialized: false,
            ..Default::default()
        };
        let rec = Expr::Record(Box::new(rec));
        symbol_table.add_local(&exprs[0], &rec)?;
        Ok(rec)
    }

    pub fn defmethod_x7(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        let rec = exprs[0].eval(symbol_table)?.get_record()?;
        rec.defmethod(exprs.skip(1), symbol_table)
    }

    fn add_method_x7(&self, exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        if self.initialized {
            bail!("Cannot add methods to initialized record {}", self.name)
        }
        let method_name = exprs[0].get_symbol_string()?;
        let method_symbol = format!("{}.{}", self.type_name(), method_name);
        let (arg_list, body) = if let Ok(doc) = exprs[1].get_string() {
            symbol_table.add_doc_item(method_symbol.clone(), doc);
            (exprs[2].get_list()?, exprs[3].clone())
        } else {
            (exprs[1].get_list()?, exprs[2].clone())
        };
        let method_fn = move |_args: Vector<Expr>, sym: &SymbolTable| body.eval(sym);
        let f = Function::new_named_args(
            method_symbol,
            arg_list.len(),
            Arc::new(method_fn),
            arg_list.iter().cloned().collect(),
            true,
            im::HashMap::new(),
        );
        self.methods.insert(method_name, f);
        Ok(Expr::Nil)
    }

    fn call_method(
        &self,
        method_name: &str,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        if !self.initialized {
            bail!(
                "Method {} called on uninitialized record {} with args [ {} ]",
                method_name,
                self.display(),
                args.iter().join(" ")
            )
        }

        // First check attributes
        if let Some(field_value) = self.fields.get(method_name) {
            return Ok(field_value.clone());
        }

        // Finally, look it up
        match self.methods.get(method_name) {
            Some(method) => {
                let augmented_sym = symbol_table.with_closure(
                    &self
                        .fields
                        .iter()
                        .map(|e| (e.key().clone(), e.value().clone()))
                        .collect(),
                );
                augmented_sym.add_item("self".into(), Expr::Record(Record::clone(self)));
                method.call_fn(args, &augmented_sym)
            }
            None => unknown_method!(self, method_name),
        }
    }
}
