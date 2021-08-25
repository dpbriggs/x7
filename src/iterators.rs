#![allow(clippy::unnecessary_wraps)]
use crate::symbols::{Expr, Function, LispResult, SymbolTable};
use im::{vector, Vector};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use rand::random;

pub type IterType = Box<dyn LazyIter>;

pub trait LazyIter: fmt::Display + fmt::Debug + Sync + Send {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>>;
    fn name(&self) -> &'static str;
    fn clone(&self) -> Box<dyn LazyIter>;
    fn id(&self) -> u64;
    fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
        let mut res = Vector::new();
        while let Some(ee) = self.next(symbol_table) {
            res.push_back(ee?)
        }
        Ok(Expr::List(res))
    }
}

impl Hash for IterType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
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
    fn id(&self) -> u64 {
        self.deref().id()
    }
}

#[derive(Clone)]
pub(crate) struct LazyMap {
    inner: IterType,
    f: Function,
    id: u64,
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

    fn id(&self) -> u64 {
        self.id
    }
}

impl LazyMap {
    pub(crate) fn lisp_res(inner: IterType, f: Function) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(LazyMap {
            inner,
            f,
            id: random(),
        })))
    }
}

#[derive(Clone)]
pub(crate) struct LazyFilter {
    inner: IterType,
    f: Function,
    id: u64,
}

impl LazyIter for LazyFilter {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        loop {
            match self.inner.next(symbol_table)? {
                Ok(item) => {
                    let pred_res = self
                        .f
                        .call_fn(Vector::unit(item.clone()), symbol_table)
                        .and_then(|fn_res| fn_res.get_bool());
                    // Result<bool, Err>
                    match pred_res {
                        Ok(false) => continue,
                        Ok(true) => return Some(Ok(item)),
                        Err(e) => return Some(Err(e)),
                    }
                }
                Err(e) => return Some(Err(e)),
            }
        }
    }

    fn name(&self) -> &'static str {
        "LazyFilter"
    }

    fn clone(&self) -> Box<dyn LazyIter> {
        Box::new(Clone::clone(self))
    }

    fn id(&self) -> u64 {
        0
    }
}

impl LazyFilter {
    pub(crate) fn lisp_res(inner: IterType, f: Function) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(LazyFilter {
            inner,
            f,
            id: random(),
        })))
    }
}

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[derive(Default, Debug)]
struct Counter(AtomicUsize);

impl Clone for Counter {
    fn clone(&self) -> Self {
        let value = self.0.load(Ordering::SeqCst);
        Counter(AtomicUsize::new(value))
    }
}

impl Counter {
    fn zero() -> Counter {
        Counter(AtomicUsize::new(0))
    }

    fn fetch_add_one(&self) -> usize {
        self.0.fetch_add(1, Ordering::SeqCst)
    }
}

#[derive(Clone)]
pub(crate) struct NaturalNumbers {
    counter: Counter,
    id: u64,
}

impl NaturalNumbers {
    pub(crate) fn lisp_res() -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(NaturalNumbers {
            counter: Counter::zero(),
            id: random(),
        })))
    }
}

impl LazyIter for NaturalNumbers {
    fn next(&self, _symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        let res = self.counter.fetch_add_one();
        // let res: usize = *self.counter.borrow();
        // *self.counter.borrow_mut() += 1;
        Some(Ok(Expr::Num((res as u64).into())))
    }

    fn name(&self) -> &'static str {
        "NaturalNumbers"
    }

    fn clone(&self) -> IterType {
        Box::new(Clone::clone(self))
    }
    fn id(&self) -> u64 {
        self.id
    }
}

use std::sync::Arc;

#[derive(Debug, Clone)]
pub(crate) struct LazyList {
    inner: Arc<Vector<Expr>>,
    index: Counter,
}

impl LazyList {
    pub(crate) fn lisp_new(inner: Vector<Expr>) -> LispResult<Expr> {
        let lazy = LazyList {
            inner: Arc::new(inner),
            index: Counter::zero(),
        };
        Ok(Expr::LazyIter(Box::new(lazy)))
    }
}

impl fmt::Display for LazyList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl LazyIter for LazyList {
    fn next(&self, _symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        self.inner.get(self.index.fetch_add_one()).cloned().map(Ok)
    }

    fn name(&self) -> &'static str {
        "Lazy"
    }

    fn clone(&self) -> Box<dyn LazyIter> {
        Box::new(Clone::clone(self))
    }

    fn id(&self) -> u64 {
        0
    }
}

#[derive(Debug)]
pub(crate) struct TakeWhile {
    pred: Function,
    inner: IterType,
    done: AtomicBool,
}

impl TakeWhile {
    pub(crate) fn lisp_res(pred: Function, inner: IterType) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(TakeWhile {
            pred,
            inner,
            done: AtomicBool::new(false),
        })))
    }
}

impl Clone for TakeWhile {
    fn clone(&self) -> Self {
        Self {
            pred: self.pred.clone(),
            inner: LazyIter::clone(&self.inner),
            done: AtomicBool::new(self.done.load(Ordering::SeqCst)),
        }
    }
}

impl fmt::Display for TakeWhile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TakeWhile<{}, {}, {}>",
            self.pred,
            self.inner,
            self.done.load(Ordering::SeqCst)
        )
    }
}

macro_rules! option_try {
    ($e:expr) => {
        match $e {
            Ok(val) => val,
            Err(e) => return Some(Err(e)),
        }
    };
}

impl LazyIter for TakeWhile {
    fn next(&self, symbol_table: &SymbolTable) -> Option<LispResult<Expr>> {
        if self.done.load(Ordering::SeqCst) {
            return None;
        }
        let res = option_try!(self.inner.next(symbol_table)?);
        let fn_res = option_try!(self
            .pred
            .call_fn(im::Vector::unit(res.clone()), symbol_table));
        let should_stop = !option_try!(fn_res.get_bool());
        if should_stop {
            self.done.store(true, Ordering::SeqCst);
            None
        } else {
            Some(Ok(res))
        }
    }

    fn name(&self) -> &'static str {
        "TakeWhile"
    }

    fn clone(&self) -> Box<dyn LazyIter> {
        Box::new(Clone::clone(self))
    }

    fn id(&self) -> u64 {
        random()
    }
}

// impl Lazy {
//     fn lisp_res(list: Vector<Expr>) -> LispResult<Expr> {
//         Ok(Expr::LazyIter(Box::new()))
//     }
// }

pub(crate) struct Take {
    inner: IterType,
    amount: AtomicUsize,
    id: u64,
}

impl Take {
    pub(crate) fn lisp_res(amount: usize, inner: IterType) -> LispResult<Expr> {
        Ok(Expr::LazyIter(Box::new(Take {
            amount: AtomicUsize::new(amount),
            inner,
            id: random(),
        })))
    }
}

impl Clone for Take {
    fn clone(&self) -> Take {
        Take {
            inner: Clone::clone(&self.inner),
            amount: AtomicUsize::new(self.amount.load(Ordering::SeqCst)),
            id: self.id,
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
    fn id(&self) -> u64 {
        self.id
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

impl_dbg_inner!(LazyMap, LazyFilter, Take);
impl_dbg!(NaturalNumbers);
