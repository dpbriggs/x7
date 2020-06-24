use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::sync::Mutex;

#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Num(f64),
    Symbol(String),
    List(Vec<Expr>),
    Function(Function),
    Nil,
    String(String),
    Quote(Vec<Expr>),
    // Bool(bool),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Nil => write!(f, "Nil"),
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
    pub(crate) fn is_even_list(&self) -> bool {
        if let Expr::List(l) = self {
            l.len() % 2 == 0
        } else {
            false
        }
    }

    pub(crate) fn is_list(&self) -> bool {
        if let Expr::List(_) = self {
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

    pub(crate) fn get_list(&self) -> LispResult<&[Expr]> {
        if let Expr::List(l) = self {
            Ok(&l)
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
}

pub(crate) type X7FunctionPtr =
    Arc<dyn for<'c> Fn(&'c [Expr], &'c SymbolTable) -> LispResult<Expr> + Sync + Send>;

#[derive(Clone)]
pub(crate) struct Function {
    symbol: String,
    minimum_args: usize,
    f: X7FunctionPtr,
    named_args: Vec<Expr>, // Expr::Symbol
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
    pub fn new(symbol: String, minimum_args: usize, f: X7FunctionPtr) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
            named_args: Vec::with_capacity(0),
        }
    }

    pub fn new_named_args(
        symbol: String,
        minimum_args: usize,
        f: X7FunctionPtr,
        named_args: Vec<Expr>,
    ) -> Self {
        Self {
            symbol,
            minimum_args,
            f,
            named_args,
        }
    }

    fn call_fn(&self, args: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
        if self.minimum_args > args.len() {
            Err(ProgramError::NotEnoughArgs)
        } else {
            if self.named_args.is_empty() {
                (self.f)(args, symbol_table)
            } else {
                let new_sym = symbol_table.with_locals(&self.named_args, args)?;
                (self.f)(args, &new_sym)
            }
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

impl std::ops::Add<&Expr> for Expr {
    type Output = LispResult<Expr>;
    fn add(self, other: &Expr) -> LispResult<Expr> {
        match (&self, &other) {
            (Expr::Num(l), Expr::Num(r)) => (Ok(Expr::Num(l + r))),
            (Expr::String(l), Expr::String(r)) => Ok(Expr::String(l.to_string() + r)),
            (Expr::List(l), Expr::List(r)) => {
                let mut res = l.clone();
                res.append(&mut r.clone());
                Ok(Expr::List(res))
            }
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

impl Expr {
    pub(crate) fn top_level_iter(self) -> Vec<Expr> {
        if let Expr::List(l) = self {
            l
        } else {
            unreachable!()
        }
    }

    pub(crate) fn call_fn(&self, args: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
        if let Expr::Function(f) = self {
            f.call_fn(args, symbol_table)
        } else {
            Err(ProgramError::NotAFunction)
        }
    }

    pub(crate) fn eval_iter<'a>(
        &'a self,
        symbol_table: &'a SymbolTable,
        start: usize,
    ) -> LispResult<EvalIter<'a>> {
        if let Expr::List(l) = self {
            let ei = EvalIter {
                inner: &l[start..],
                symbol_table,
            };
            Ok(ei)
        } else {
            Err(ProgramError::BadTypes)
        }
    }

    pub(crate) fn eval(&self, symbol_table: &SymbolTable) -> LispResult<Expr> {
        if self.is_list() {
            // eval list
            let list = self.get_list()?;
            if list.is_empty() {
                return Ok(Expr::List(Vec::with_capacity(0)));
            }

            let head = list[0].clone();
            let tail = &list[1..];

            return head.eval(&symbol_table)?.call_fn(&tail, symbol_table);
        }

        // Resolve Symbol

        if self.is_symbol() {
            // TODO: Use symbol table reference
            return symbol_table.lookup(&self);
        }

        Ok(self.clone())
    }
}

pub(crate) struct EvalIter<'a> {
    inner: &'a [Expr],
    symbol_table: &'a SymbolTable,
}

impl<'a> Iterator for EvalIter<'a> {
    type Item = LispResult<Expr>;

    fn next(&mut self) -> Option<Self::Item> {
        dbg!(self.inner);
        if self.inner.len() == 0 {
            None
        } else {
            let res = self.inner[0].eval(self.symbol_table);
            self.inner = &self.inner[1..];
            dbg!(&res);
            if res.is_ok() {
                Some(res.unwrap().eval(self.symbol_table))
            } else {
                Some(res)
            }
        }
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

    pub(crate) fn lookup(&self, key: &Expr) -> LispResult<Expr> {
        // Check Functions
        let symbol = match key {
            Expr::Symbol(ref s) => s,
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

    pub(crate) fn add<'a>(
        &'a mut self,
        values: impl Iterator<Item = &'a [Expr]>,
    ) -> LispResult<()> {
        let mut new_layer = SymbolLookup::new();
        for pair in values {
            if pair.len() != 2 {
                panic!("pairs len needs to be two");
            }
            let symbol = match pair[0] {
                Expr::Symbol(ref s) => s,
                _ => return Err(ProgramError::CannotLookupNonSymbol),
            };
            new_layer.insert(symbol.to_string(), pair[1].clone());
        }
        self.locals.push(new_layer);
        Ok(())
    }

    pub(crate) fn add_global_fn(&self, f: Function) {
        let symbol = f.symbol.clone();
        let expr = Expr::Function(f); // TODO: Scope inheritance?
        let mut guard = GLOBAL_SYMS.lock().unwrap();
        guard.insert(symbol, expr);
    }

    pub(crate) fn with_locals(&self, symbols: &[Expr], values: &[Expr]) -> LispResult<Self> {
        let mut copy = self.clone();
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
        copy.locals.push(locals);
        Ok(copy)
    }
}

fn get_symbol(sym: Option<Expr>) -> Option<LispResult<String>> {
    match sym {
        Some(rest_sym) => Some(rest_sym.get_symbol_string()),
        None => None,
    }
}