use crate::iterators::IterType;
use anyhow::{anyhow, bail, Context};
use bigdecimal::{BigDecimal, ToPrimitive, Zero};
use core::cell::RefCell;
use core::cmp::Ordering;
use im::Vector;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::Mutex;

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

pub type Num = BigDecimal;

#[derive(Clone)]
pub(crate) enum Expr {
    Num(Num),
    Symbol(String),
    List(Vector<Expr>),
    Function(Function),
    Nil,
    String(String),
    Quote(Vector<Expr>),
    Tuple(Vector<Expr>),
    Bool(bool),
    LazyIter(IterType),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Num(l), Expr::Num(r)) => l.eq(r),
            (Expr::Symbol(l), Expr::Symbol(r)) => l.eq(r),
            (Expr::String(l), Expr::String(r)) => l.eq(r),
            (Expr::List(l), Expr::List(r)) => l.eq(r),
            (Expr::Tuple(l), Expr::Tuple(r)) => l.eq(r),
            (Expr::Function(l), Expr::Function(r)) => l.eq(r),
            (Expr::Quote(l), Expr::Quote(r)) => l.eq(r),
            (Expr::Bool(l), Expr::Bool(r)) => l.eq(r),
            (Expr::LazyIter(_), Expr::LazyIter(_)) => false,
            (Expr::Nil, Expr::Nil) => true,
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
            Expr::Symbol(s) => write!(f, "{}", s),
            Expr::Function(ff) => write!(f, "{}", ff),
            Expr::LazyIter(i) => write!(f, "{}", i),
            Expr::Quote(l) => write!(f, "'({})", debug_join(l)),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::List(l) => write!(f, "({})", debug_join(l)),
            Expr::Tuple(l) => write!(f, "(tuple {})", debug_join(l)),
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

impl Expr {
    pub(crate) fn full_order_list(&self) -> LispResult<Vector<Expr>> {
        let list = self.get_list()?;
        if list.is_empty() {
            Ok(list)
        } else {
            let head = &list[0];
            if !list.iter().skip(1).all(|e| match (head, e) {
                (Expr::Num(_), Expr::Num(_)) => true,
                (Expr::String(_), Expr::String(_)) => true,
                _ => false,
            }) {
                // only floats (sorta) + strings are totally ordered
                bad_types!("list of identically typed, ordered elements", &self)
            } else {
                Ok(list)
            }
        }
    }

    pub(crate) fn get_type_str(&self) -> &'static str {
        match self {
            Expr::Num(_) => "num",
            Expr::String(_) => "str",
            Expr::Quote(_) => "quote",
            Expr::Bool(_) => "bool",
            Expr::Function(_) => "func",
            Expr::Symbol(_) => "symbol",
            Expr::List(_) => "list",
            Expr::Nil => "nil",
            Expr::LazyIter(_) => "iterator",
            Expr::Tuple(_) => "tuple",
        }
    }

    pub(crate) fn get_num(&self) -> LispResult<Num> {
        if let Expr::Num(n) = self {
            Ok(n.clone())
        } else {
            bad_types!("num", &self)
        }
    }

    pub(crate) fn get_usize(&self) -> LispResult<usize> {
        let res = self.get_num()?.to_usize().ok_or(anyhow!(
            "Cannot represent {} as it needs to fit in a usize",
            self.get_num()?
        ))?;
        Ok(res)
    }

    pub(crate) fn get_string(&self) -> LispResult<String> {
        if let Expr::String(s) = self {
            Ok(s.clone())
        } else {
            bad_types!("string", &self)
        }
    }

    pub(crate) fn is_bool_true(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            bad_types!("bool", &self)
        }
    }

    pub(crate) fn is_tuple(&self) -> bool {
        if let Expr::Tuple(_) = self {
            true
        } else {
            false
        }
    }

    pub(crate) fn is_symbol(&self) -> bool {
        if let Expr::Symbol(_) = self {
            true
        } else {
            false
        }
    }

    pub(crate) fn get_function(&self) -> LispResult<Function> {
        if let Expr::Function(f) = self {
            Ok(f.clone())
        } else {
            bad_types!("func", &self)
        }
    }

    pub(crate) fn get_iterator(&self) -> LispResult<IterType> {
        if let Expr::LazyIter(l) = self {
            Ok(l.clone())
        } else {
            bad_types!("iterator", &self)
        }
    }

    pub(crate) fn get_bool(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            bad_types!("bool", &self)
            // Err(ProgramError::BadTypes).with_context(|| format!("{} is not a bool!", &self))
        }
    }

    pub(crate) fn get_quote(&self) -> LispResult<Vector<Expr>> {
        if let Expr::Quote(l) = self {
            Ok(l.clone())
        } else {
            bad_types!("quote", &self)
        }
    }

    pub(crate) fn get_list(&self) -> LispResult<Vector<Expr>> {
        if let Expr::List(l) = self {
            Ok(l.clone())
        } else if let Expr::Nil = self {
            Ok(Vector::new())
        } else if let Expr::Tuple(l) = self {
            Ok(l.clone())
        } else {
            bad_types!("list", &self)
        }
    }

    pub(crate) fn symbol_matches(&self, sym: &'static str) -> bool {
        if let Expr::Symbol(s) = self {
            s == sym
        } else {
            false
        }
    }

    pub(crate) fn get_symbol_string(&self) -> LispResult<String> {
        if let Expr::Symbol(s) = self {
            Ok(s.clone())
        } else {
            bad_types!("symbol", &self)
        }
    }

    pub(crate) fn rename_function(self, new_name: String) -> LispResult<Expr> {
        if let Expr::Function(mut f) = self {
            f.symbol = new_name;
            Ok(Expr::Function(f))
        } else {
            bad_types!("function", &self)
        }
    }
}

pub(crate) type X7FunctionPtr =
    Arc<dyn Fn(Vector<Expr>, &SymbolTable) -> LispResult<Expr> + Sync + Send>;

#[derive(Clone)]
pub(crate) struct Function {
    symbol: String,
    minimum_args: usize,
    f: X7FunctionPtr,
    named_args: Vec<Expr>, // Expr::Symbol
    eval_args: bool,
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

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Function {
    pub fn new(symbol: String, minimum_args: usize, f: X7FunctionPtr, eval_args: bool) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
            named_args: Vec::with_capacity(0),
            eval_args,
        }
    }

    pub fn new_named_args(
        symbol: String,
        minimum_args: usize,
        f: X7FunctionPtr,
        named_args: Vec<Expr>,
        eval_args: bool,
    ) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
            named_args,
            eval_args,
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

        if self.named_args.is_empty() {
            if self.eval_args {
                let args: Vector<_> = args.iter().map(|e| e.eval(symbol_table)).try_collect()?;
                // let args = args?;
                return (self.f)(args.clone(), symbol_table).with_context(|| {
                    format!("Error in {}, with args {}", &self, format_args(&args))
                });
            } else {
                return (self.f)(args, symbol_table);
            }
        }

        let args = if self.eval_args {
            let args: Vector<_> = args.iter().map(|e| e.eval(symbol_table)).try_collect()?;
            args
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

// use thiserror::Error;

#[derive(Debug, PartialEq)]
pub(crate) enum ProgramError {
    BadTypes, // context
    CannotLookupNonSymbol,
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

pub(crate) type LispResult<T> = anyhow::Result<T>;

impl std::ops::Rem<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn rem(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l % r))),
            _ => bad_types!(format!(
                "Remainder requires left and right are num types, was given {} % {}",
                &self, &other
            )),
        }
    }
}

impl std::ops::Add<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn add(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l + r))),
            (Expr::String(l), Expr::String(r)) => Ok(Expr::String(l.to_string() + r)),
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
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l - r))),
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
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l * r))),
            (Expr::String(l), Expr::Num(r)) => {
                if *r >= BigDecimal::zero() {
                    Ok(Expr::String(
                        l.to_string().repeat(Expr::Num(r.clone()).get_usize()?),
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
                    Ok(Expr::Num(l / r))
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
            (Expr::String(l), Expr::String(r)) => l.partial_cmp(r),
            _ => None,
        }
    }
}

impl Eq for Expr {}

impl Ord for Expr {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Expr::Num(l), Expr::Num(r)) => l.partial_cmp(r).unwrap(),
            (Expr::String(l), Expr::String(r)) => l.cmp(r),
            _ => panic!("bad types {:?} {:?}", self, other),
        }
    }
}

impl Expr {
    pub(crate) fn call_fn(
        &self,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        if let Expr::Function(f) = self {
            f.call_fn(args, symbol_table)
        } else {
            bail!(ProgramError::NotAFunction(self.clone()));
        }
    }

    pub(crate) fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
        // Tuple bypass

        if self.is_tuple() {
            return Ok(self.clone());
        }

        // Eval List

        if let Ok(mut list) = self.get_list() {
            if list.is_empty() {
                return Ok(Expr::List(Vector::new()));
            }

            let head = list.pop_front().unwrap();
            let tail = list;

            return head.eval(&symbol_table)?.call_fn(tail, symbol_table);
        }

        // Eval quote

        if let Ok(list) = self.get_quote() {
            return Ok(Expr::List(list));
        }

        // Resolve Symbol

        if self.is_symbol() {
            return symbol_table.lookup(&self);
        }

        Ok(self.clone())
    }
}

use once_cell::sync::Lazy;

static GLOBAL_SYMS: Lazy<Mutex<HashMap<String, Expr>>> = Lazy::new(|| Mutex::new(HashMap::new()));
static CANONICAL_DOC_ORDER: Lazy<Mutex<Vec<String>>> = Lazy::new(|| Default::default());

type SymbolLookup = HashMap<String, Expr>;

// TODO: Debug should include stdlib
#[derive(Clone, Debug)]
pub struct SymbolTable {
    locals: RefCell<Vec<SymbolLookup>>,
    docs: Arc<Mutex<HashMap<String, String>>>,
}

impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {
            locals: RefCell::new(Vec::with_capacity(0)),
            docs: Default::default(),
        }
    }

    pub(crate) fn lookup(&self, key: &Expr) -> LispResult<Expr> {
        // Check Functions
        let symbol = match key {
            Expr::Symbol(ref s) => s,
            _ => bail!(ProgramError::CannotLookupNonSymbol),
        };
        for scope in self.locals.borrow().iter().rev() {
            if let Some(expr) = scope.get(symbol) {
                return Ok(expr.clone());
            }
        }
        // Check global scope
        let guard = GLOBAL_SYMS.lock().unwrap();
        guard
            .get(symbol)
            .cloned()
            .ok_or_else(|| anyhow!("Unknown Symbol {}", symbol.to_string()))
    }

    pub(crate) fn add_local(&self, symbol: &Expr, value: &Expr) -> LispResult<Expr> {
        let mut locals = self.locals.borrow_mut();
        if locals.is_empty() {
            locals.push(SymbolLookup::new());
        }
        locals
            .last_mut()
            .unwrap()
            .insert(symbol.get_symbol_string()?, value.clone());
        Ok(Expr::Nil)
    }

    pub(crate) fn add_global_fn(&self, f: Function) {
        let symbol = f.symbol.clone();
        let expr = Expr::Function(f); // TODO: Scope inheritance?
        let mut guard = GLOBAL_SYMS.lock().unwrap();
        guard.insert(symbol, expr);
    }

    pub(crate) fn add_doc_item(&self, symbol: String, doc: String) {
        let mut guard = self.docs.lock().unwrap();
        guard.insert(symbol, doc);
    }

    pub(crate) fn get_doc_item(&self, symbol: &str) -> Option<String> {
        let guard = self.docs.lock().unwrap();
        guard.get(symbol).cloned()
    }

    pub(crate) fn with_locals(&self, symbols: &[Expr], values: Vector<Expr>) -> LispResult<Self> {
        let copy = self.clone();
        let mut locals = SymbolLookup::new();
        let mut symbol_iter = symbols.iter().cloned();
        let mut values_iter = values.iter().cloned();
        // TODO: Find nicer way to express argument collapsing.
        #[allow(clippy::while_let_loop)]
        loop {
            let symbol = if let Some(sym) = get_symbol(symbol_iter.next()) {
                sym?
            } else {
                break;
            };

            if symbol == "&" {
                let rest_sym = if let Some(sym) = get_symbol(symbol_iter.next()) {
                    sym?
                } else {
                    bail!(ProgramError::ExpectedRestSymbol);
                };
                locals.insert(rest_sym, Expr::List(values_iter.collect()));
                break;
            }

            let value = values_iter.next().unwrap();
            locals.insert(symbol, value);
        }
        copy.locals.borrow_mut().push(locals);
        Ok(copy)
    }

    pub(crate) fn push_canonical_doc_item(item: String) {
        let mut guard = CANONICAL_DOC_ORDER.lock().unwrap();
        guard.push(item);
    }
    pub(crate) fn get_canonical_doc_order() -> Vec<String> {
        let guard = CANONICAL_DOC_ORDER.lock().unwrap();
        let ret = (*guard).clone();
        ret
    }
}

// (fn foo (x & rest) ...)
// (foo 1 2 3 4) // x: 1, rest: '(2 3 4)

fn get_symbol(sym: Option<Expr>) -> Option<LispResult<String>> {
    match sym {
        Some(rest_sym) => Some(rest_sym.get_symbol_string()),
        None => None,
    }
}

fn format_args(args: &Vector<Expr>) -> String {
    // let mut res = String::new();
    format!("{}{}{}", "(", debug_join(args), ")")
}
