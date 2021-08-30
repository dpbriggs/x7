#![allow(clippy::match_like_matches_macro)]
use crate::interner::InternedString;
use crate::iterators::IterType;
use crate::records::RecordType;
use anyhow::{anyhow, bail, Context};
use bigdecimal::{BigDecimal, FromPrimitive, ToPrimitive, Zero};
use core::cmp::Ordering;
use im::Vector;
use itertools::Itertools;
use parking_lot::RwLock;
use std::collections::HashMap;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::sync::Arc;

#[macro_export]
macro_rules! bad_types {
    ($custom:expr) => {
        Err(anyhow!(ProgramError::BadTypes)).with_context(|| $custom)
    };

    ($expected:expr, $given:expr) => {
        Err(anyhow!(ProgramError::BadTypes)).with_context(|| {
            format!(
                "Error: Expected {}, but got type '{}': {:?}",
                $expected,
                $given.get_type_str(),
                $given
            )
        })
    };
}

pub type Integer = i64;
pub type Num = BigDecimal;
pub type Dict = im::HashMap<Expr, Expr>;
pub type Symbol = InternedString;

#[allow(clippy::derive_hash_xor_eq)] // It's probably OK.
#[derive(Clone, Hash)]
pub enum Expr {
    Num(Num),
    Integer(Integer),
    Symbol(Symbol),
    List(Vector<Expr>),
    Function(Arc<Function>),
    Nil,
    String(String),
    Quote(Vector<Expr>),
    Tuple(Vector<Expr>),
    Bool(bool),
    LazyIter(IterType),
    Dict(Dict),
    Record(crate::records::RecordType),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Num(l), Expr::Num(r)) => l.eq(r),
            (Expr::Integer(l), Expr::Integer(r)) => l.eq(r),
            (Expr::Symbol(l), Expr::Symbol(r)) => l.eq(r),
            (Expr::String(l), Expr::String(r)) => l.eq(r),
            (Expr::List(l), Expr::List(r)) => l.eq(r),
            (Expr::Tuple(l), Expr::Tuple(r)) => l.eq(r),
            (Expr::Function(l), Expr::Function(r)) => l.eq(r),
            (Expr::Quote(l), Expr::Quote(r)) => l.eq(r),
            (Expr::Bool(l), Expr::Bool(r)) => l.eq(r),
            (Expr::LazyIter(_), Expr::LazyIter(_)) => false,
            (Expr::Nil, Expr::Nil) => true,
            (Expr::Dict(l), Expr::Dict(r)) => l.eq(r),
            (Expr::Record(l), Expr::Record(r)) => l.eq(r),
            _ => false,
        }
    }
}

fn debug_join(exprs: &Vector<Expr>) -> String {
    exprs
        .iter()
        .map(|s| format!("{:?}", s))
        .collect::<Vec<String>>()
        .join(" ")
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nil => write!(f, "nil"),
            Expr::String(s) => write!(f, "\"{}\"", s),
            Expr::Num(n) => write!(f, "{}", n),
            Expr::Integer(n) => write!(f, "{}", n),
            Expr::Symbol(s) => write!(f, "{}", s),
            Expr::Function(ff) => write!(f, "{}", ff),
            Expr::LazyIter(i) => write!(f, "{}", i),
            Expr::Quote(l) => write!(f, "'({})", debug_join(l)),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::List(l) => write!(f, "({})", debug_join(l)),
            Expr::Tuple(l) => write!(f, "(tuple {})", debug_join(l)),
            Expr::Dict(l) => write!(f, "{:?}", l),
            Expr::Record(l) => write!(f, "{:?}", l),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::String(s) => write!(f, "{}", s),
            rest => write!(f, "{:?}", rest),
        }
    }
}

pub(crate) trait ToNumericExpr {
    fn to_expr(self) -> Expr;
    fn to_bigdecimal(self) -> Num;
}

impl ToNumericExpr for usize {
    #[inline]
    fn to_expr(self) -> Expr {
        Expr::Num(FromPrimitive::from_usize(self).unwrap())
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        FromPrimitive::from_usize(self).unwrap()
    }
}

impl ToNumericExpr for u64 {
    #[inline]
    fn to_expr(self) -> Expr {
        Expr::Num(FromPrimitive::from_u64(self).unwrap())
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        FromPrimitive::from_u64(self).unwrap()
    }
}

impl ToNumericExpr for u32 {
    #[inline]
    fn to_expr(self) -> Expr {
        Expr::Num(FromPrimitive::from_u32(self).unwrap())
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        FromPrimitive::from_u32(self).unwrap()
    }
}

impl ToNumericExpr for i32 {
    #[inline]
    fn to_expr(self) -> Expr {
        Expr::Integer(self as Integer)
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        FromPrimitive::from_i32(self).unwrap()
    }
}

impl ToNumericExpr for Integer {
    #[inline]
    fn to_expr(self) -> Expr {
        Expr::Integer(self)
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        FromPrimitive::from_i64(self).unwrap()
    }
}

impl ToNumericExpr for BigDecimal {
    #[inline]
    fn to_expr(self) -> Expr {
        if self.is_integer() {
            match self.to_i64() {
                Some(i) => Expr::Integer(i),
                None => Expr::Num(self),
            }
        } else {
            Expr::Num(self)
        }
    }

    #[inline]
    fn to_bigdecimal(self) -> Num {
        self
    }
}

impl Expr {
    pub(crate) fn full_order_list(&self) -> LispResult<Vector<Expr>> {
        let list = self.get_list()?;
        if list.is_empty() {
            Ok(list)
        } else {
            let head = &list[0];
            if !list.iter().skip(1).all(|e| match (head, e) {
                (Expr::Num(_), Expr::Num(_)) => true,
                (Expr::Integer(_), Expr::Integer(_)) => true,
                (Expr::Num(_), Expr::Integer(_)) => true,
                (Expr::Integer(_), Expr::Num(_)) => true,
                (Expr::String(_), Expr::String(_)) => true,
                _ => false,
            }) {
                // only floats (sorta) + strings are totally ordered
                bad_types!("list of identically typed, ordered elements", self)
            } else {
                Ok(list)
            }
        }
    }

    #[inline]
    pub(crate) fn num<T: ToNumericExpr>(number: T) -> Self {
        number.to_expr()
    }

    pub(crate) fn function(f: Function) -> Self {
        Expr::Function(Arc::new(f))
    }

    pub(crate) fn get_type_str(&self) -> &'static str {
        match self {
            Expr::Num(_) => "num",
            Expr::String(_) => "str",
            Expr::Quote(_) => "quote",
            Expr::Integer(_) => "int",
            Expr::Bool(_) => "bool",
            Expr::Function(_) => "func",
            Expr::Symbol(_) => "symbol",
            Expr::List(_) => "list",
            Expr::Nil => "nil",
            Expr::LazyIter(_) => "iterator",
            Expr::Tuple(_) => "tuple",
            Expr::Dict(_) => "map",
            Expr::Record(_) => "record",
        }
    }

    pub(crate) fn get_num(&self) -> LispResult<Num> {
        match self {
            Expr::Num(n) => Ok(n.clone()),
            Expr::Integer(n) => Ok(n.to_bigdecimal()),
            _ => bad_types!("num", self),
        }
    }

    pub(crate) fn get_record(&self) -> LispResult<RecordType> {
        if let Expr::Record(r) = self {
            Ok(r.clone())
        } else {
            bad_types!("record", self)
        }
    }

    pub(crate) fn get_usize(&self) -> LispResult<usize> {
        let res = self.get_num()?.to_usize().ok_or(anyhow!(
            "Cannot represent {} as it needs to fit in a usize",
            self.get_num()?
        ))?;
        Ok(res)
    }

    pub fn get_symbol(&self) -> LispResult<Symbol> {
        if let Expr::Symbol(s) = self {
            Ok(*s)
        } else {
            bad_types!("symbol", self)
        }
    }

    pub fn get_string(&self) -> LispResult<String> {
        if let Expr::String(s) = self {
            Ok(s.clone())
        } else {
            bad_types!("string", self)
        }
    }

    pub(crate) fn get_dict(&self) -> LispResult<Dict> {
        if let Expr::Dict(d) = self {
            Ok(d.clone())
        } else {
            bad_types!("dict", self)
        }
    }

    pub(crate) fn is_symbol_underscore(&self) -> bool {
        self.get_symbol_string()
            .ok()
            .map(|s| s.to_string() == "_")
            .unwrap_or(false)
    }

    pub(crate) fn is_bool_true(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            bad_types!("bool", self)
        }
    }

    pub(crate) fn len(&self) -> LispResult<usize> {
        let len = match self {
            Expr::List(l) => l.len(),
            Expr::Tuple(l) => l.len(),
            Expr::Quote(l) => l.len(),
            Expr::Dict(m) => m.len(),
            Expr::String(s) => s.len(),
            Expr::Symbol(s) => s.len(),
            _ => return bad_types!("collection", self),
        };
        Ok(len)
    }

    #[inline]
    pub(crate) fn get_function(&self) -> LispResult<&Function> {
        if let Expr::Function(f) = self {
            Ok(f)
        } else {
            bad_types!("func", self)
        }
    }

    #[inline]
    pub(crate) fn is_iterator(&self) -> bool {
        match self {
            Expr::LazyIter(_) => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn get_iterator(&self) -> LispResult<IterType> {
        if let Expr::LazyIter(l) = self {
            Ok(l.clone())
        } else {
            bad_types!("iterator", self)
        }
    }

    #[inline]
    pub(crate) fn get_bool(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            bad_types!("bool", self)
        }
    }

    // HACK: This is a very ugly. Should remove.
    #[inline]
    pub(crate) fn push_front(&self, item: Expr) -> LispResult<Expr> {
        let mut list = self.get_list()?;
        list.push_front(item);
        let res = match self {
            Expr::List(_) => Expr::List(list),
            Expr::Quote(_) => Expr::Quote(list),
            Expr::Tuple(_) => Expr::Tuple(list),
            _ => unreachable!(),
        };
        Ok(res)
    }

    #[inline]
    pub(crate) fn get_list(&self) -> LispResult<Vector<Expr>> {
        if let Expr::List(l) = self {
            Ok(l.clone())
        } else if let Expr::Nil = self {
            Ok(Vector::new())
        } else if let Expr::Tuple(l) = self {
            Ok(l.clone())
        } else {
            bad_types!("list", self)
        }
    }

    #[inline]
    pub(crate) fn symbol_matches(&self, sym: &'static str) -> bool {
        if let Expr::Symbol(s) = self {
            s == sym
        } else {
            false
        }
    }

    #[inline]
    pub fn get_symbol_string(&self) -> LispResult<InternedString> {
        if let Expr::Symbol(s) = self {
            Ok(*s)
        } else {
            bad_types!("symbol", self)
        }
    }
}

pub(crate) type X7FunctionPtr =
    Arc<dyn Fn(Vector<Expr>, &SymbolTable) -> LispResult<Expr> + Sync + Send>;

#[derive(Clone)]
pub struct Function {
    pub symbol: InternedString,
    pub minimum_args: usize,
    f: X7FunctionPtr,
    pub named_args: Vec<Expr>, // Expr::Symbol
    eval_args: bool,
    closure: Option<HashMap<InternedString, Expr>>,
}

use std::hash::{Hash, Hasher};

impl Hash for Function {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
        self.minimum_args.hash(state);
        self.named_args.hash(state);
        self.eval_args.hash(state);
    }
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        // TODO: See if this is an issue. This should only appear in
        // one code generation unit (i.e. this crate), so it should be safe.
        #[allow(clippy::vtable_address_comparisons)]
        Arc::ptr_eq(&self.f, &other.f)
    }
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fn<{}, {}, [ ", self.symbol, self.minimum_args)?;
        for arg in &self.named_args {
            let sym = arg.get_symbol_string().unwrap_or_else(|_| "??".into());
            write!(f, "{} ", sym)?;
        }
        write!(f, "]>")
    }
}

macro_rules! try_collect {
    ($args:expr, $symbol_table:expr) => {{
        let mut args_clone = $args;
        for arg in args_clone.iter_mut() {
            *arg = arg.eval(&$symbol_table)?;
        }
        args_clone
    }};
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Function {
    pub fn new(symbol: String, minimum_args: usize, f: X7FunctionPtr, eval_args: bool) -> Self {
        Self {
            symbol: symbol.into(),
            minimum_args,
            f,
            named_args: Vec::with_capacity(0),
            eval_args,
            closure: None,
        }
    }

    pub fn new_named_args(
        symbol: InternedString,
        minimum_args: usize,
        f: X7FunctionPtr,
        named_args: Vec<Expr>,
        eval_args: bool,
        closure: HashMap<InternedString, Expr>,
    ) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
            named_args,
            eval_args,
            closure: Some(closure),
        }
    }

    // TODO: Refactor this into something cleaner.
    pub(crate) fn call_fn(
        &self,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        if self.minimum_args > args.len() {
            bail!(anyhow!(
                "Too few args supplied for {}. Expected {}, was given {} of length {}",
                &self,
                self.minimum_args,
                args.iter().join(" "),
                args.len()
            ));
        }

        let closure;
        let mut symbol_table = symbol_table;

        // TODO: Turn this into something less nasty.
        if let Some(close) = &self.closure {
            closure = Some(symbol_table.with_closure(close));
            symbol_table = closure.as_ref().unwrap();
        }
        // let symbol_table = match &self.closure {
        //     None => symbol_table.clone(),
        //     Some(close) => ,
        // };

        if self.named_args.is_empty() {
            if self.eval_args {
                let args = try_collect!(args, symbol_table);
                return (self.f)(args.clone(), symbol_table).with_context(|| {
                    format!("Error in {}, with args {}", &self, format_args(&args))
                });
            } else {
                return (self.f)(args, symbol_table);
            }
        }

        let args = if self.eval_args {
            try_collect!(args, symbol_table)
        } else {
            args
        };

        // Add local variables to symbol table
        let new_sym = symbol_table.with_locals(&self.named_args, args.clone())?;

        // Call the function
        (self.f)(args.clone(), &new_sym)
            .with_context(|| format!("Error in {}, with args {}", &self, format_args(&args)))
    }
}

impl std::error::Error for ProgramError {}

#[derive(Debug, PartialEq)]
pub(crate) enum ProgramError {
    BadTypes, // context
    // InvalidCharacterInSymbol,
    // CannotStartExprWithNonSymbol,
    CondNoExecutionPath,
    CondBadConditionNotEven,
    DivisionByZero,
    // FailedToParseInt,
    // FailedToParseString,
    NotAFunction(Expr),
    // NotAList,
    // NotEnoughArgs(usize),
    // NotImplementedYet,
    ExpectedRestSymbol,
    // UnexpectedEOF,
    WrongNumberOfArgs(usize),
    FailedToParse(String),
    // Custom(String),
}

impl fmt::Display for ProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub type LispResult<T> = anyhow::Result<T>;

impl std::ops::Rem<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn rem(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::num(l % r))),
            (Expr::Integer(l), Expr::Integer(r)) => (Ok(Expr::num(l % r))),
            (Expr::Integer(l), Expr::Num(r)) => (Ok(Expr::num(l.to_bigdecimal() % r))),
            (Expr::Num(l), Expr::Integer(r)) => (Ok(Expr::num(l % r.to_bigdecimal()))),
            _ => bad_types!(format!(
                "Remainder requires left and right are num types, was given {:?} % {:?}",
                &self, &other
            )),
        }
    }
}

impl std::ops::Add<&Expr> for Expr {
    type Output = LispResult<Expr>;
    #[inline]
    fn add(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::num(l + r))),
            (Expr::Integer(l), Expr::Integer(r)) => match l.checked_add(*r) {
                Some(res) => Ok(Expr::num(res)),
                None => Ok(Expr::num(l.to_bigdecimal() + r.to_bigdecimal())),
            },
            (Expr::Integer(l), Expr::Num(r)) => Ok(Expr::num(l.to_bigdecimal() + r)),
            (Expr::Num(l), Expr::Integer(r)) => Ok(Expr::num(l + r.to_bigdecimal())),
            (Expr::String(l), Expr::String(r)) => Ok(Expr::String(l.to_string() + r)),
            (Expr::Num(l), Expr::String(r)) => (Ok(Expr::String(format!("{}{}", l, r)))),
            (Expr::String(l), Expr::Num(r)) => (Ok(Expr::String(format!("{}{}", l, r)))),
            (Expr::List(l), Expr::List(r)) => {
                let mut res = l.clone();
                res.append(r.clone());
                Ok(Expr::List(res))
            }
            (Expr::Tuple(l), Expr::Tuple(r)) => {
                let mut res = l.clone();
                res.append(r.clone());
                Ok(Expr::Tuple(res))
            }
            (Expr::List(l), Expr::Nil) => Ok(Expr::List(l.clone())),
            (Expr::Nil, Expr::List(r)) => Ok(Expr::List(r.clone())),
            (Expr::Nil, Expr::Nil) => Ok(Expr::Nil),
            _ => bad_types!(format!(
                "Addition between these types doesn't make sense: {} + {}",
                &self, other
            )),
        }
    }
}

impl std::ops::Sub<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn sub(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::num(l - r))),
            (Expr::Integer(l), Expr::Integer(r)) => match l.checked_sub(*r) {
                Some(res) => Ok(Expr::num(res)),
                None => Ok(Expr::num(l.to_bigdecimal() - r.to_bigdecimal())),
            },
            (Expr::Integer(l), Expr::Num(r)) => Ok(Expr::num(l.to_bigdecimal() - r)),
            (Expr::Num(l), Expr::Integer(r)) => Ok(Expr::num(l - r.to_bigdecimal())),
            _ => bad_types!(format!(
                "Subtraction between these types doesn't make sense: {} - {}",
                &self, other
            )),
        }
    }
}

impl std::ops::Mul<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn mul(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::num(l * r))),
            (Expr::Integer(l), Expr::Integer(r)) => match l.checked_mul(*r) {
                Some(res) => Ok(Expr::num(res)),
                None => Ok(Expr::Num(l.to_bigdecimal() * r.to_bigdecimal())), // res is larger than i64
            },
            (Expr::Integer(l), Expr::Num(r)) => Ok(Expr::num(l.to_bigdecimal() * r)),
            (Expr::Num(l), Expr::Integer(r)) => Ok(Expr::num(l * r.to_bigdecimal())),
            (Expr::String(l), Expr::Num(r)) => {
                if *r >= BigDecimal::zero() {
                    Ok(Expr::String(
                        l.to_string().repeat(Expr::num(r.clone()).get_usize()?),
                    ))
                } else {
                    bad_types!(format!(
                        "Repeating a string negative times doesn't make sense: {} * {}",
                        &self, other
                    ))
                }
            }
            _ => bad_types!(format!(
                "Multiplication between these types doesn't make sense: {} * {}",
                &self, other
            )),
        }
    }
}

impl std::ops::Div<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn div(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => {
                if *r == BigDecimal::zero() {
                    bail!(ProgramError::DivisionByZero);
                } else {
                    Ok(Expr::num(l / r))
                }
            }
            (_, Expr::Integer(0)) => bail!(ProgramError::DivisionByZero),
            (Expr::Integer(l), Expr::Integer(r)) => {
                Ok(Expr::num(l.to_bigdecimal() / r.to_bigdecimal()))
            }
            (Expr::Num(l), Expr::Integer(r)) => Ok(Expr::num(l / r.to_bigdecimal())),
            (Expr::Integer(l), Expr::Num(r)) => {
                if *r == BigDecimal::zero() {
                    bail!(ProgramError::DivisionByZero)
                } else {
                    Ok(Expr::num(l.to_bigdecimal() / r))
                }
            }
            _ => bad_types!(format!(
                "Division between these types doesn't make sense: {} / {}",
                &self, other
            )),
        }
    }
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Expr) -> Option<Ordering> {
        match (self, other) {
            (Expr::Num(l), Expr::Num(r)) => l.partial_cmp(r),
            (Expr::Integer(l), Expr::Integer(r)) => l.partial_cmp(r),
            (Expr::Num(l), Expr::Integer(r)) => l.partial_cmp(&r.to_bigdecimal()),
            (Expr::Integer(l), Expr::Num(r)) => l.to_bigdecimal().partial_cmp(r),
            (Expr::String(l), Expr::String(r)) => l.partial_cmp(r),
            _ => None,
        }
    }
}

impl Eq for Expr {}

impl Ord for Expr {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Expr::Num(l), Expr::Num(r)) => l.cmp(r),
            (Expr::Integer(l), Expr::Integer(r)) => l.cmp(r),
            (Expr::Num(l), Expr::Integer(r)) => l.cmp(&r.to_bigdecimal()),
            (Expr::Integer(l), Expr::Num(r)) => l.to_bigdecimal().cmp(r),
            (Expr::String(l), Expr::String(r)) => l.cmp(r),
            _ => Ordering::Less,
        }
    }
}

impl Expr {
    #[inline]
    pub(crate) fn call_fn(
        &self,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        match self {
            Expr::Function(f) => f.call_fn(args, symbol_table),
            Expr::Record(r) => r.call_as_fn(args, symbol_table),
            _ => bail!(ProgramError::NotAFunction(self.clone())),
        }
    }

    pub fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
        let res = match self {
            Expr::Symbol(sym) => {
                return symbol_table.lookup(sym);
            }
            Expr::List(list) => {
                let head = match list.get(0) {
                    Some(h) => h,
                    None => return Ok(Expr::List(Vector::new())),
                };
                let tail = list.clone().slice(1..);
                return head.eval(symbol_table)?.call_fn(tail, symbol_table);
            }
            tup @ Expr::Tuple(_) => tup.clone(),
            Expr::Quote(inner) => Expr::List(inner.clone()),
            otherwise => otherwise.clone(),
        };
        Ok(res)
    }
}

use std::sync::Mutex;

#[derive(Debug, Clone, Default)]
struct Doc {
    docs: HashMap<String, String>,
    order: Vec<String>,
}

impl Doc {
    fn with_globals(v: Vec<(String, String)>) -> Self {
        let mut docs = HashMap::new();
        for (name, doc) in v.iter().cloned() {
            docs.insert(name, doc);
        }
        let order = v.into_iter().map(|(name, _)| name).collect();
        Doc { docs, order }
    }

    fn add(&mut self, name: String, doc: String) {
        self.docs.insert(name.clone(), doc);
        self.order.push(name)
    }
}

// TODO: Debug should include stdlib
#[derive(Clone, Debug, Default)]
pub struct SymbolTable {
    globals: Arc<RwLock<HashMap<InternedString, Expr>>>,
    locals: Arc<RwLock<HashMap<InternedString, Expr>>>,
    docs: Arc<Mutex<Doc>>,
    // TODO: Should functions be magic like this?
    // Future Dave: magic means we special case adding
    // symbols to the table whether or not a function is calling.
    // So named arguments last only as long as the function calling.
    func_locals: HashMap<InternedString, Expr>,
}

impl SymbolTable {
    pub(crate) fn with_globals(
        globals: Vec<(String, Expr)>,
        doc_order: Vec<(String, String)>,
    ) -> SymbolTable {
        SymbolTable {
            globals: Arc::new(RwLock::new(
                globals
                    .into_iter()
                    .map(|(s, e)| (InternedString::new(s), e))
                    .collect(),
            )),
            locals: Default::default(),
            docs: Arc::new(Mutex::new(Doc::with_globals(doc_order))),
            func_locals: Default::default(),
        }
    }

    pub(crate) fn lookup(&self, symbol: &InternedString) -> LispResult<Expr> {
        if let Some(expr) = self.func_locals.get(symbol) {
            return Ok(expr.clone());
        }
        if let Some(expr) = self.locals.read().get(symbol) {
            return Ok(expr.clone());
        }
        // Check global scope
        self.globals
            .read()
            .get(symbol)
            .cloned()
            .ok_or_else(|| anyhow!("Unknown Symbol {}", symbol.to_string()))
    }

    pub(crate) fn symbol_exists(&self, sym: &InternedString) -> bool {
        self.lookup(sym).is_ok()
    }

    pub(crate) fn get_func_locals(&self) -> HashMap<InternedString, Expr> {
        self.func_locals.clone()
    }

    pub(crate) fn with_closure(&self, other: &HashMap<InternedString, Expr>) -> SymbolTable {
        SymbolTable {
            func_locals: self
                .func_locals
                .iter()
                .chain(other)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            ..self.clone()
        }
    }

    pub(crate) fn add_local_item(&self, symbol: InternedString, value: Expr) -> Self {
        let new = self.clone();
        new.locals.write().insert(symbol, value);
        new
    }

    pub(crate) fn add_symbol(&self, sym: InternedString, value: Expr) {
        self.locals.write().insert(sym, value);
    }

    pub(crate) fn add_local(&self, symbol: &Expr, value: &Expr) -> LispResult<Expr> {
        self.locals
            .write()
            .insert(symbol.get_symbol_string()?, value.clone());
        Ok(Expr::Nil)
    }

    pub(crate) fn add_doc_item(&self, symbol: String, doc: String) {
        let mut guard = self.docs.lock().unwrap();
        guard.add(symbol, doc);
    }

    pub(crate) fn get_doc_item(&self, symbol: &str) -> Option<String> {
        let guard = self.docs.lock().unwrap();
        guard.docs.get(symbol).cloned()
    }

    pub(crate) fn get_doc_methods(&self, sym: &str) -> Vec<(String, String)> {
        let guard = self.docs.lock().unwrap();
        let sym = format!("{}.", sym);
        guard
            .docs
            .iter()
            .filter(|(symbol, _doc)| symbol.starts_with(&sym))
            .map(|(symbol, doc)| (symbol.into(), doc.into()))
            .collect()
    }

    pub(crate) fn query_symbol_starts_with(&self, prefix: &str) -> Vec<String> {
        let guard = self.globals.read();
        guard
            .iter()
            .chain(self.locals.read().iter())
            .filter(|(s, _)| s.to_string().starts_with(prefix))
            .map(|(hit, _)| hit.to_string())
            .collect()
    }

    pub(crate) fn with_locals(&self, symbols: &[Expr], values: Vector<Expr>) -> LispResult<Self> {
        let mut copy = self.clone();
        let mut symbol_iter = symbols.iter().cloned();
        let mut values_iter = values.iter().cloned();
        let new_func_locals = &mut copy.func_locals;
        // TODO: Find nicer way to express argument collapsing.
        #[allow(clippy::while_let_loop)]
        loop {
            let symbol = if let Some(sym) = get_symbol(symbol_iter.next()) {
                sym?
            } else {
                break;
            };

            if symbol.to_string() == "&" {
                let rest_sym = if let Some(sym) = get_symbol(symbol_iter.next()) {
                    sym?
                } else {
                    bail!(ProgramError::ExpectedRestSymbol);
                };
                copy.locals
                    .write()
                    .insert(rest_sym, Expr::List(values_iter.collect()));
                break;
            }

            let value = values_iter.next().unwrap();
            new_func_locals.insert(symbol, value);
        }
        Ok(copy)
    }

    pub(crate) fn get_canonical_doc_order(&self) -> Vec<String> {
        let guard = self.docs.lock().unwrap();
        guard.order.clone()
    }

    pub(crate) fn load_file<P: AsRef<Path>>(&self, path: P) -> LispResult<Expr> {
        let mut strbuf = String::new();
        File::open(path)?.read_to_string(&mut strbuf)?;
        for expr in crate::parser::read(strbuf.as_str()) {
            let prog = expr?;
            prog.eval(self)?;
        }
        Ok(Expr::Nil)
    }
}

// (fn foo (x & rest) ...)
// (foo 1 2 3 4) // x: 1, rest: '(2 3 4)

fn get_symbol(sym: Option<Expr>) -> Option<LispResult<InternedString>> {
    sym.map(|s| s.get_symbol_string())
}

fn format_args(args: &Vector<Expr>) -> String {
    // let mut res = String::new();
    format!("{}{}{}", "(", debug_join(args), ")")
}
