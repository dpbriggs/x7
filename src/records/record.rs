use crate::symbols::{Expr, LispResult};
use core::hash::Hash;
use core::hash::Hasher;
use im::Vector;
use std::fmt;
use std::ops::Deref;

pub(crate) type RecordType = Box<dyn Record>;

pub(crate) trait RecordDoc {
    fn name() -> &'static str;
    fn type_doc() -> &'static str;
    fn method_doc() -> Vec<(&'static str, &'static str)>;
}

pub(crate) trait Record: Sync + Send {
    fn call_method(&self, sym: &str, args: Vector<Expr>) -> LispResult<Expr>;
    fn id(&self) -> u64 {
        0
    }
    fn display(&self) -> String;
    fn debug(&self) -> String;
    fn clone(&self) -> RecordType;
    fn methods(&self) -> &'static [&'static str] {
        &[]
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
    fn call_method(&self, sym: &str, args: Vector<Expr>) -> LispResult<Expr> {
        self.deref().call_method(sym, args)
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
    fn methods(&self) -> &'static [&'static str] {
        self.deref().methods()
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
            "Unknown method `{}` for {}\n\nHelp: It has the following methods\n\n{}",
            $method,
            $self.display(),
            $self
                .methods()
                .iter()
                .map(|s| format!("- {}", s))
                .join("\n")
        ))
    }};
}
