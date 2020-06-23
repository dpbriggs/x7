#![allow(unused)]
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::Mutex;

#[derive(Clone, Debug)]
pub(crate) enum DataType {
    Num(f64),
    Symbol(String),
    List(Vec<Expr>),
    Function(Function),
    Nil,
    String(String),
    Quote(Vec<Expr>),
    // Bool(bool),
}

impl fmt::Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataType::Nil => write!(f, "Nil"),
            DataType::String(s) => write!(f, "\"{}\"", s),
            DataType::Num(n) => write!(f, "{}", n),
            DataType::Symbol(s) => write!(f, "{}", s),
            // DataType::Bool(b) => write!(f, "{}", b),
            DataType::Function(ff) => write!(f, "{}", ff),
            DataType::Quote(l) => {
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
            DataType::List(l) => {
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

impl DataType {
    // XXX: HACK
    fn is_quote(&self) -> bool {
        if let DataType::Function(f) = self {
            if f.symbol == "quote" {
                return true;
            }
        }
        false
    }
    fn is_list(&self) -> bool {
        if let DataType::List(_) = self {
            true
        } else {
            false
        }
    }

    fn is_symbol(&self) -> bool {
        if let DataType::Symbol(_) = self {
            true
        } else {
            false
        }
    }

    fn get_list(&self) -> &[Expr] {
        if let DataType::List(l) = self {
            &l
        } else {
            unreachable!()
        }
    }

    pub(crate) fn coll_iter(&self) -> LispResult<impl Iterator<Item = &Expr>> {
        if let DataType::List(l) = self {
            Ok(l.iter())
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    // fn first_n<'a>(&'a self, amount: usize) -> &'a [Expr] {
    // }

    fn call_fn(&self, args: &[Expr]) -> LispResult<Expr> {
        if let DataType::Function(f) = self {
            f.call_fn(args)
        } else {
            Err(ProgramError::NotAFunction)
        }
    }
}

#[derive(Clone)]
pub(crate) struct Function {
    symbol: String,
    minimum_args: usize,
    f: Arc<dyn Fn(&[Expr]) -> LispResult<Expr> + Sync + Send>,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fn<{}, {}>", self.symbol, self.minimum_args)
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Function {
    pub fn new(
        symbol: String,
        minimum_args: usize,
        f: Arc<dyn Fn(&[Expr]) -> LispResult<Expr> + Sync + Send>,
    ) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
        }
    }

    fn call_fn(&self, args: &[Expr]) -> LispResult<Expr> {
        if self.minimum_args > args.len() {
            Err(ProgramError::NotEnoughArgs)
        } else {
            (self.f)(args)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ProgramError {
    BadTypes,
    CannotLookupNonSymbol,
    // CannotStartExprWithNonSymbol,
    // CondBadConditionNotEven,
    DivisionByZero,
    FailedToParseInt,
    FailedToParseString,
    NotAFunction,
    NotAList,
    NotEnoughArgs,
    NotImplementedYet,
    UnexpectedEOF,
    UnknownSymbol,
    WrongNumberOfArgs,
}

pub type LispResult<T> = Result<T, ProgramError>;

#[derive(Clone, Debug)]
pub(crate) struct Expr {
    pub dataty: DataType,
    symbol_table: SymbolTable,
}

impl std::ops::Add<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn add(self, other: &Expr) -> LispResult<Expr> {
        match (&self.dataty, &other.dataty) {
            (DataType::Num(l), DataType::Num(r)) => (self.bind(DataType::Num(l + r))),
            (DataType::String(l), DataType::String(r)) => {
                self.bind(DataType::String(l.to_string() + r))
            }
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl std::ops::Sub<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn sub(self, other: &Expr) -> LispResult<Expr> {
        match (&self.dataty, &other.dataty) {
            (DataType::Num(l), DataType::Num(r)) => (self.bind(DataType::Num(l - r))),
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl std::ops::Mul<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn mul(self, other: &Expr) -> LispResult<Expr> {
        match (&self.dataty, &other.dataty) {
            (DataType::Num(l), DataType::Num(r)) => (self.bind(DataType::Num(l * r))),
            (DataType::String(l), DataType::Num(r)) => {
                if *r >= 0.0 {
                    self.bind(DataType::String(l.to_string().repeat(r.trunc() as usize)))
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
        match (&self.dataty, &other.dataty) {
            (DataType::Num(l), DataType::Num(r)) => {
                if *r == 0.0 {
                    Err(ProgramError::DivisionByZero)
                } else {
                    self.bind(DataType::Num(l / r))
                }
            }
            _ => Err(ProgramError::BadTypes),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.dataty.fmt(f)
    }
}

impl Expr {
    pub(crate) fn new(dataty: DataType) -> Expr {
        Self {
            symbol_table: SymbolTable::new(),
            dataty,
        }
    }

    pub(crate) fn nil() -> Expr {
        Expr::new(DataType::Nil)
    }

    pub(crate) fn list(l: Vec<Expr>) -> Expr {
        Expr::new(DataType::List(l))
    }

    pub(crate) fn func(l: Function) -> Expr {
        Expr::new(DataType::Function(l))
    }

    pub(crate) fn quote(q: Vec<Expr>) -> Expr {
        Expr::new(DataType::Quote(q))
    }

    pub(crate) fn top_level_iter(self) -> Vec<Expr> {
        if let DataType::List(l) = self.dataty {
            l
        } else {
            unreachable!()
        }
    }

    pub fn list_iter(&self) -> LispResult<Vec<Expr>> {
        match &self.dataty {
            DataType::List(l) => Ok(l.to_vec()),
            // TODO: Figure out quotes
            // DataType::Quote(q) => q.iter().cloned().map(|e| e.eval())
            _ => Err(ProgramError::NotAList),
        }
    }

    pub fn bind(&self, dataty: DataType) -> LispResult<Expr> {
        let expr = Expr {
            symbol_table: self.symbol_table.clone(),
            dataty,
        };
        Ok(expr)
    }

    pub(crate) fn call_fn(&self, args: &[Expr]) -> LispResult<Expr> {
        self.dataty.call_fn(args)
    }

    pub(crate) fn eval(&self) -> LispResult<Expr> {
        if self.dataty.is_list() {
            // eval list
            let list = self.dataty.get_list();
            if list.is_empty() {
                return self.bind(DataType::List(Vec::with_capacity(0)));
            }

            // TODO: Is there a more efficient way to do this?
            let mut iter = list.iter().map(|expr| expr.eval());
            let head = iter.next().unwrap()?;

            // TODO: Is there a better way to do this?
            // e.g. use '(1 2 3)
            // XXX: There needs a better way to lazily process symbols.
            if head.dataty.is_quote() {
                return self.bind(DataType::Quote(self.dataty.get_list()[1..].into()));
            }

            let tail: Vec<Expr> = iter.collect::<Result<Vec<Expr>, ProgramError>>()?;
            return head.dataty.call_fn(&tail);
        }

        // Resolve Symbol

        if self.dataty.is_symbol() {
            return self.symbol_table.lookup(&self.dataty);
        }

        Ok(self.clone())
    }
}

use once_cell::sync::Lazy;

static GLOBAL_SYMS: Lazy<Mutex<HashMap<String, Expr>>> = Lazy::new(|| Mutex::new(HashMap::new()));

type SymbolLookup = HashMap<String, Expr>;

#[derive(Clone, Debug)]
pub(crate) struct SymbolTable {
    locals: Vec<SymbolLookup>,
}

impl SymbolTable {
    pub(crate) fn new() -> SymbolTable {
        SymbolTable {
            locals: Vec::with_capacity(0),
        }
    }

    pub(crate) fn lookup(&self, key: &DataType) -> LispResult<Expr> {
        // Check Functions
        let symbol = match key {
            DataType::Symbol(ref s) => s,
            _ => return Err(ProgramError::CannotLookupNonSymbol),
        };
        for scope in self.locals.iter().rev() {
            if let Some(expr) = scope.get(symbol) {
                return Ok(expr.clone());
            }
        }
        // Check global scope
        let guard = GLOBAL_SYMS.lock().unwrap();
        guard
            .get(symbol)
            .cloned()
            .ok_or(ProgramError::UnknownSymbol)
    }

    pub(crate) fn add_global_fn(&mut self, f: Function) {
        let symbol = f.symbol.clone();
        let expr = Expr::new(DataType::Function(f)); // TODO: Scope inheritance?
        let mut guard = GLOBAL_SYMS.lock().unwrap();
        guard.insert(symbol, expr);
    }
}
