use crate::symbols::{Expr, LispResult, ProgramError, SymbolTable};
use anyhow::bail;
use core::hash::Hash;
use core::hash::Hasher;
use im::Vector;
use std::fmt;
use std::ops::Deref;

pub(crate) type RecordType = Box<dyn Record>;

/// Document Records. Used in the document_records! macro
/// to properly document your record type.
pub(crate) trait RecordDoc {
    /// Public name of the the record.
    fn name() -> &'static str;
    /// Documentation for that record type.
    fn type_doc() -> &'static str;
    /// Documentation of the methods.
    /// (method_name, method_doc)
    fn method_doc() -> &'static [(&'static str, &'static str)];
}

/// Fundamental trait for records.
///
/// Records allow x7 to represent a variety of internally mutable types
/// while not expanding the Expr enum too much. These types are responsible for
/// implementing RecordDoc if they want to have documentation.
pub trait Record: Sync + Send {
    /// Call a method on this record.
    /// (.method_name <rec> arg1 arg2 arg3)
    /// Becomes:
    /// (&self: <rec>, sym: "method_name", args: vector![arg1, arg2, arg3])
    fn call_method(
        &self,
        sym: &str,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr>;
    fn id(&self) -> u64 {
        0
    }
    /// Nicely display the record type.
    fn display(&self) -> String;
    /// Add more information for debug printing
    fn debug(&self) -> String;
    /// Clone the object.
    fn clone(&self) -> RecordType;
    /// Return the names of the methods for help messages.
    fn methods(&self) -> Vec<String>;
    /// Return the type name for nice help messages
    fn type_name(&self) -> String;

    fn call_as_fn(&self, _args: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
        bail!(ProgramError::NotAFunction(Expr::Record(Box::new(
            self.clone(),
        ))))
    }

    fn defmethod(&self, _args: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
        bail!(
            "Defining methods is not supported on this record: {}",
            Record::type_name(self)
        )
    }
}

impl fmt::Display for RecordType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display())
    }
}

impl fmt::Debug for RecordType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.debug())
    }
}

impl Record for RecordType {
    fn call_method(
        &self,
        sym: &str,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        self.deref().call_method(sym, args, symbol_table)
    }

    fn debug(&self) -> String {
        self.deref().debug()
    }

    fn display(&self) -> String {
        self.deref().display()
    }

    fn id(&self) -> u64 {
        self.deref().id()
    }
    fn clone(&self) -> RecordType {
        self.deref().clone()
    }
    fn methods(&self) -> Vec<String> {
        self.deref().methods()
    }
    fn type_name(&self) -> String {
        self.deref().type_name()
    }
    fn call_as_fn(&self, args: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        self.deref().call_as_fn(args, symbol_table)
    }
    fn defmethod(&self, args: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        self.deref().defmethod(args, symbol_table)
    }
}

impl Hash for RecordType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

impl PartialEq for RecordType {
    fn eq(&self, _other: &RecordType) -> bool {
        false
    }
}

impl Clone for RecordType {
    fn clone(&self) -> RecordType {
        Record::clone(self)
    }
}

#[macro_export]
macro_rules! record {
    ($e:expr) => {
        Ok(Expr::Record(Box::new($e)))
    };
}

#[macro_export]
macro_rules! unknown_method {
    ($self:expr, $method:expr) => {{
        use itertools::Itertools;
        Err(anyhow!(
            "Unknown method `{}` on {}\n\nHelp! {} has the following methods:\n\n{}",
            $method,
            $self.display(),
            $self.type_name(),
            $self
                .methods()
                .iter()
                .map(|s| format!("- {}", s))
                .join("\n")
        ))
    }};
}

#[macro_export]
macro_rules! try_call_method {
    ($self:expr, $sym:expr, $args:expr, $($method_name:ident),*) => {
        match $sym {
            $(
                stringify!($method_name) => $self.$method_name($args),
            )*
                _ => unknown_method!($self, $sym)
        }
    }
}
