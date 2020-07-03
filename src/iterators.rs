use crate::symbols::{Expr, Function, LispResult, Num, SymbolTable};
use im::Vector;
use std::fmt;
use std::ops::Deref;

pub(crate) type IterType = Box<dyn LazyIter>;

pub(crate) trait LazyIter: fmt::Display + fmt::Debug + Sync + Send {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>>;
    fn name(&self) -> &'static str;
    fn clone(&self) -> Box<dyn LazyIter>;
    fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
        let mut res = Vector::new();
        while let Some(ee) = self.next(symbol_table) {
            res.push_back(ee?)
        }
        Ok(Expr::List(res))
    }
}

impl PartialEq for IterType {
    fn eq(&self, _other: &IterType) -> bool {
        false
    }
}

impl Clone for Box<dyn LazyIter> {
    fn clone(&self) -> Box<dyn LazyIter> {
        LazyIter::clone(self)
    }
}

impl LazyIter for IterType {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        self.deref().next(symbol_table)
    }
    fn name(&self) -> &'static str {
        self.deref().name()
    }
    fn clone(&self) -> IterType {
        self.deref().clone()
    }
}

// impl<T: IterType> Clone for

#[derive(Clone)]
pub(crate) struct LazyMap {
    inner: IterType,
    f: Function,
}

impl LazyIter for LazyMap {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        self.inner
            .next(symbol_table)
            .map(|lispres| lispres.and_then(|e| self.f.call_fn(Vector::unit(e), symbol_table)))
    }
    fn name(&self) -> &'static str {
        "Map"
    }
    fn clone(&self) -> IterType {
        Box::new(Clone::clone(self))
    }
}

impl LazyMap {
    pub(crate) fn new(inner: IterType, f: Function) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(LazyMap { inner, f })))
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

pub(crate) struct NaturalNumbers {
    counter: AtomicUsize,
}

impl Clone for NaturalNumbers {
    fn clone(&self) -> NaturalNumbers {
        NaturalNumbers {
            counter: AtomicUsize::new(self.counter.load(Ordering::SeqCst)),
        }
    }
}

impl NaturalNumbers {
    pub(crate) fn new() -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(NaturalNumbers {
            counter: AtomicUsize::new(0),
        })))
    }
}

impl LazyIter for NaturalNumbers {
    fn next(&self, _symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        let res = self.counter.fetch_add(1, Ordering::SeqCst);
        // let res: usize = *self.counter.borrow();
        // *self.counter.borrow_mut() += 1;
        Some(Ok(Expr::Num(res as Num)))
    }

    fn name(&self) -> &'static str {
        "NaturalNumbers"
    }

    fn clone(&self) -> IterType {
        Box::new(Clone::clone(self))
    }
}

pub(crate) struct Take {
    inner: IterType,
    amount: AtomicUsize,
}

impl Take {
    pub(crate) fn new(amount: usize, inner: IterType) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(Take {
            amount: AtomicUsize::new(amount),
            inner,
        })))
    }
}

impl Clone for Take {
    fn clone(&self) -> Take {
        Take {
            inner: Clone::clone(&self.inner),
            amount: AtomicUsize::new(self.amount.load(Ordering::SeqCst)),
        }
    }
}

impl LazyIter for Take {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        if self.amount.load(Ordering::SeqCst) == 0 {
            None
        } else {
            self.amount.fetch_sub(1, Ordering::SeqCst);
            self.inner.next(symbol_table)
        }
    }
    fn name(&self) -> &'static str {
        "Take"
    }
    fn clone(&self) -> IterType {
        Box::new(Clone::clone(self))
    }
}

macro_rules! impl_dbg_inner {
	  ($($t:ident),*) => {
		    $(
            impl fmt::Debug for $t {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "{}<{}>", self.name(), self.inner)
                }
            }
            impl fmt::Display for $t {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "{}<{}>", self.name(), self.inner)
                }
            }

        )*
	  };
}

macro_rules! impl_dbg {
	  ($($t:ident),*) => {
		    $(
            impl fmt::Debug for $t {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "LazyIter<{}>", self.name())
                }
            }
            impl fmt::Display for $t {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "LazyIter<{}>", self.name())
                }
            }
        )*
	  };
}

impl_dbg_inner!(LazyMap, Take);
impl_dbg!(NaturalNumbers);
