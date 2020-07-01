use core::cell::RefCell;
use core::cmp::Ordering;
use im::Vector;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::Mutex;

pub type Num = f64;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Expr {
    Num(Num),
    Symbol(String),
    List(Vector<Expr>),
    Function(Function),
    Nil,
    String(String),
    Quote(Vector<Expr>),
    Bool(bool),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nil => write!(f, "()"),
            Expr::String(s) => write!(f, "\"{}\"", s),
            Expr::Num(n) => write!(f, "{}", n),
            Expr::Symbol(s) => write!(f, "{}", s),
            // DataType::Bool(b) => write!(f, "{}", b),
            Expr::Function(ff) => write!(f, "{}", ff),
            Expr::Quote(l) => {
                write!(f, "'")?;
                let mut first = true;
                write!(f, "(")?;
                for item in l {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                    first = false;
                }
                write!(f, ")")?;
                Ok(())
            }
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::List(l) => {
                let mut first = true;
                write!(f, "(")?;
                for item in l {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", item)?;
                    first = false;
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

impl Expr {
    #[must_use]
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
                Err(ProgramError::BadTypes) // only floats (sorta) + strings are totally ordered
            } else {
                Ok(list)
            }
        }
    }

    pub(crate) fn get_num(&self) -> LispResult<Num> {
        if let Expr::Num(n) = self {
            Ok(*n)
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn is_bool_true(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn is_even_list(&self) -> bool {
        if let Expr::List(l) = self {
            l.len() % 2 == 0
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

    pub(crate) fn get_bool(&self) -> LispResult<bool> {
        if let Expr::Bool(b) = self {
            Ok(*b)
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn get_quote(&self) -> LispResult<Vector<Expr>> {
        if let Expr::Quote(l) = self {
            Ok(l.clone())
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn get_list(&self) -> LispResult<Vector<Expr>> {
        if let Expr::List(l) = self {
            Ok(l.clone())
        } else if let Expr::Nil = self {
            Ok(Vector::new())
        } else {
            Err(ProgramError::BadTypes)
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
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn rename_function(self, new_name: String) -> LispResult<Expr> {
        if let Expr::Function(mut f) = self {
            f.symbol = new_name;
            Ok(Expr::Function(f))
        } else {
            Err(ProgramError::BadTypes)
        }
    }
}

pub(crate) type X7FunctionPtr =
    Arc<dyn for<'c> Fn(Vector<Expr>, &'c SymbolTable) -> LispResult<Expr> + Sync + Send>;

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
        Arc::ptr_eq(&self.f, &other.f)
    }
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AnonFn<{}, {}>", self.symbol, self.minimum_args)
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
    fn call_fn(&self, args: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        if self.minimum_args > args.len() {
            return Err(ProgramError::NotEnoughArgs);
        }
        if self.named_args.is_empty() {
            if self.eval_args {
                let args: Result<Vector<_>, _> =
                    args.iter().map(|e| e.eval(symbol_table)).collect();
                return (self.f)(args?, symbol_table);
            } else {
                return (self.f)(args, symbol_table);
            }
        }
        if self.eval_args {
            let args: Result<Vector<_>, _> = args.iter().map(|e| e.eval(symbol_table)).collect();
            let args = args?;
            let new_sym = symbol_table.with_locals(&self.named_args, args.clone())?;
            (self.f)(args, &new_sym)
        } else {
            let new_sym = symbol_table.with_locals(&self.named_args, args.clone())?;
            (self.f)(args, &new_sym)
        }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) enum ProgramError {
    BadTypes,
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
    NotEnoughArgs,
    NotImplementedYet,
    // UnexpectedEOF,
    UnknownSymbol(String),
    WrongNumberOfArgs,
    FailedToParse(String),
    Custom(String),
}

pub(crate) type LispResult<T> = Result<T, ProgramError>;

impl std::ops::Rem<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn rem(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l % r))),
            _ => Err(ProgramError::BadTypes),
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
            // TODO: no clone
            (Expr::List(l), Expr::Nil) => Ok(Expr::List(l.clone())),
            (Expr::Nil, Expr::List(r)) => Ok(Expr::List(r.clone())),
            (Expr::Nil, Expr::Nil) => Ok(Expr::Nil),
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl std::ops::Sub<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn sub(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l - r))),
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl std::ops::Mul<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn mul(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l * r))),
            (Expr::String(l), Expr::Num(r)) => {
                if *r >= 0.0 {
                    Ok(Expr::String(l.to_string().repeat(r.trunc() as usize)))
                } else {
                    Err(ProgramError::NotImplementedYet)
                }
            }
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl std::ops::Div<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn div(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => {
                if *r == 0.0 {
                    Err(ProgramError::DivisionByZero)
                } else {
                    Ok(Expr::Num(l / r))
                }
            }
            _ => Err(ProgramError::BadTypes),
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
            Err(ProgramError::NotAFunction(self.clone()))
        }
    }

    pub(crate) fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
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

type SymbolLookup = HashMap<String, Expr>;

// TODO: Debug should include stdlib
#[derive(Clone, Debug)]
pub(crate) struct SymbolTable {
    locals: RefCell<Vec<SymbolLookup>>,
}

impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {
            locals: RefCell::new(Vec::with_capacity(0)),
        }
    }

    pub(crate) fn lookup(&self, key: &Expr) -> LispResult<Expr> {
        // Check Functions
        let symbol = match key {
            Expr::Symbol(ref s) => s,
            _ => return Err(ProgramError::CannotLookupNonSymbol),
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
            .ok_or_else(|| ProgramError::UnknownSymbol(symbol.to_string()))
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

    pub(crate) fn add_global_const(&self, symbol: String, value: Expr) {
        let mut guard = GLOBAL_SYMS.lock().unwrap();
        guard.insert(symbol, value);
    }

    pub(crate) fn with_locals(&self, symbols: &[Expr], values: Vector<Expr>) -> LispResult<Self> {
        let copy = self.clone();
        let mut locals = SymbolLookup::new();
        let mut symbol_iter = symbols.iter().cloned();
        let mut values_iter = values.iter().cloned();
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
                    return Err(ProgramError::NotEnoughArgs);
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
}

fn get_symbol(sym: Option<Expr>) -> Option<LispResult<String>> {
    match sym {
        Some(rest_sym) => Some(rest_sym.get_symbol_string()),
        None => None,
    }
}
