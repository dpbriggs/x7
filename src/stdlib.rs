use crate::repl::read;
use crate::symbols::{Expr, Function, LispResult, ProgramError, SymbolTable};

macro_rules! exact_len {
    ($args:expr, $len:literal) => {
        if $args.len() != $len {
            return Err(ProgramError::WrongNumberOfArgs);
        }
    };
}

// ARITHMETIC

fn lt_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs[1..].iter().all(|e| first < e);
    Ok(Expr::Bool(rest))
}

fn lte_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs[1..].iter().all(|e| first <= e);
    Ok(Expr::Bool(rest))
}

fn gt_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs[1..].iter().all(|e| first > e);
    Ok(Expr::Bool(rest))
}

fn gte_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs[1..].iter().all(|e| first >= e);
    Ok(Expr::Bool(rest))
}

fn rem_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    exprs[0].clone() % &exprs[1]
}

fn or(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        if expr.get_bool()? {
            return Ok(Expr::Bool(true));
        }
    }
    Ok(Expr::Bool(false))
}

fn and(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        if !expr.get_bool()? {
            return Ok(Expr::Bool(false));
        }
    }
    Ok(Expr::Bool(true))
}

fn not(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::Bool(!exprs[0].get_bool()?))
}

fn eq_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let all_eq = exprs.windows(2).all(|x| x[0] == x[1]);
    Ok(Expr::Bool(all_eq))
}

fn add_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc + x)
}

fn sub_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc - x)
}

fn mult_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc * x)
}

fn div_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc / x)
}

fn inc_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() > 1 {
        Err(ProgramError::WrongNumberOfArgs)
    } else if let Expr::Num(n) = exprs[0] {
        Ok(Expr::Num(n + 1.0))
    } else {
        Err(ProgramError::BadTypes)
    }
}

// MISC

fn ident(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs.into()))
}

fn quote(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Quote(exprs.into()))
}

fn apply(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    exprs[0].call_fn(exprs[1].get_list()?, symbol_table)
}

fn def(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    symbol_table.add_local(&exprs[0], &exprs[1].eval(symbol_table)?)
}

fn exprs_do(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in &exprs[0..exprs.len() - 1] {
        if let Err(e) = expr.eval(symbol_table) {
            println!("{:?}", e);
        }
    }
    exprs[exprs.len() - 1].eval(symbol_table)
}

// PRINT

fn print(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        print!("{}", expr);
    }
    Ok(Expr::Num(exprs.len() as f64))
}

fn println(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        println!("{}", expr);
    }
    Ok(Expr::Num(exprs.len() as f64))
}

// FUNC

fn cond(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() % 2 != 0 {
        return Err(ProgramError::CondBadConditionNotEven);
    }
    for pair in exprs.chunks_exact(2) {
        let (pred, body) = (&pair[0], &pair[1]);
        if pred.eval(symbol_table)?.is_bool_true()? {
            return body.eval(symbol_table);
        }
    }
    Err(ProgramError::CondNoExecutionPath)
}

fn map(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    // TODO: Performance fix this entire thing
    if exprs.len() != 2 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let f = &exprs[0];
    let mut res = Vec::with_capacity(exprs.len() - 1);
    for expr in exprs[1].get_list()? {
        res.push(f.call_fn(&[expr.clone()], symbol_table)?);
    }
    Ok(Expr::List(res))
}

/// reduce
/// (f init coll)
fn reduce(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 && exprs.len() != 3 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let f = &exprs[0];
    let mut init = exprs[1].clone();
    for item in exprs[2].get_list()? {
        init = f.call_fn(&[init, item.clone()], symbol_table)?;
    }
    Ok(init)
}

fn bind(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let symbols = &exprs[0];
    if !symbols.is_even_list() {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let sym_copy = symbol_table.clone();
    for pair in symbols.get_list()?.chunks_exact(2) {
        let (l, r) = (&pair[0], &pair[1]);
        sym_copy.add_local(l, &r.eval(&sym_copy)?)?;
    }
    exprs[1].eval(&sym_copy)
}

fn func(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let arg_symbols = exprs[0].get_list()?;
    let min_args = match arg_symbols.iter().position(|e| e.symbol_matches("&")) {
        Some(index) => index,
        None => arg_symbols.len(),
    };
    let body = exprs[1].clone();
    let f = Arc::new(move |_args: &[Expr], sym: &SymbolTable| body.eval(sym));
    let f = Function::new_named_args(
        "AnonFn".to_string(),
        min_args,
        f,
        arg_symbols.to_vec(),
        true,
    );
    Ok(Expr::Function(f))
}

fn defn(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    let name = &exprs[0];
    let func = func(&exprs[1..], symbol_table)?.rename_function(name.get_symbol_string()?)?;
    def(&[name.clone(), func.clone()], symbol_table)?;
    Ok(func)
}

// LISTS

fn list(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs.into()))
}

fn cons(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let mut list: Vec<_> = exprs[1].get_list()?.into();
    let mut res = Vec::with_capacity(list.len() + 1);
    res.push(exprs[0].clone());
    res.append(&mut list);
    Ok(Expr::List(res))
}

fn head(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let list = exprs[0].get_list()?;
    if list.is_empty() {
        Ok(Expr::Nil)
    } else {
        Ok(list[0].clone())
    }
}

fn tail(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let list = exprs[0].get_list()?;
    if list.is_empty() {
        Ok(Expr::Nil)
    } else {
        Ok(Expr::List(list[1..].into()))
    }
}

fn range(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let num = exprs[0].get_num()?.trunc();
    if num < 0.0 {
        Err(ProgramError::Custom(format!(
            "Cannot have a negative range {}",
            num
        )))
    } else {
        let list = (0..num as usize).map(|n| Expr::Num(n as f64)).collect();
        Ok(Expr::List(list))
    }
}

fn shuffle(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let mut list = exprs[0].get_list()?.to_vec();
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    list.shuffle(&mut thread_rng());
    Ok(Expr::List(list))
}

fn len(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::Num(exprs[0].get_list()?.len() as f64))
}

use std::sync::Arc;

macro_rules! make_stdlib_fns {
	  ( $(($sym:literal, $minargs:expr, $func:ident, $eval_args:expr)),* ) => {
        {
            let syms = SymbolTable::new();
            $(
		            syms.add_global_fn(Function::new($sym.into(), $minargs, Arc::new($func), $eval_args));
            )*
            syms
        }
	  };
}

macro_rules! make_stdlib_consts {
    ($syms:expr, $(($sym:literal, $value:expr)),*) => {
        {
            $(
                $syms.add_global_const($sym.into(), $value);
            )*
        $syms
        }
    }
}

#[allow(clippy::let_and_return)]
pub(crate) fn create_stdlib_symbol_table() -> SymbolTable {
    let syms = make_stdlib_fns!(
        // ARITHMETIC
        ("+", 1, add_exprs, true),
        ("-", 1, sub_exprs, true),
        ("*", 1, mult_exprs, true),
        ("%", 2, rem_exprs, true),
        ("/", 2, div_exprs, true),
        ("=", 1, eq_exprs, true),
        ("<", 2, lt_exprs, true),
        ("<=", 2, lte_exprs, true),
        (">", 2, gt_exprs, true),
        (">=", 2, gte_exprs, true),
        ("inc", 1, inc_exprs, true),
        ("not", 1, not, true),
        ("or", 1, or, true),
        ("and", 1, and, true),
        // // MISC
        ("ident", 0, ident, true),
        ("quote", 0, quote, false),
        ("print", 1, print, true),
        ("println", 1, println, true),
        ("def", 1, def, false),
        ("cond", 2, cond, false),
        ("shuffle", 1, shuffle, true),
        // FUNC TOOLS
        ("map", 1, map, true),
        ("apply", 2, apply, true),
        ("do", 1, exprs_do, false),
        ("reduce", 2, reduce, true),
        // Functions
        ("fn", 0, func, false),
        ("defn", 3, defn, false),
        ("bind", 2, bind, false),
        // Lists
        ("list", 0, list, true),
        ("head", 1, head, true),
        ("tail", 1, tail, true),
        ("cons", 2, cons, true),
        ("range", 1, range, true),
        ("len", 1, len, true)
    );
    // syms
    let syms = make_stdlib_consts!(
        syms,
        ("true", Expr::Bool(true)),
        ("false", Expr::Bool(false))
    );
    load_x7_stdlib(syms).unwrap()
}

use std::fs::File;
use std::io;
use std::io::prelude::*;

// TODO: Modules
// TODO: Descuff interpreter loading
fn load_x7_stdlib(symbol_table: SymbolTable) -> io::Result<SymbolTable> {
    let mut stdlib_str = String::new();
    File::open("stdlib/base.x7")?.read_to_string(&mut stdlib_str)?;
    let prog = match read(stdlib_str.as_str()) {
        Ok(p) => p,
        Err(e) => {
            panic!("{:?}", e);
        }
    };
    for expr in prog.top_level_iter() {
        let res = match expr.eval(&symbol_table) {
            Ok(p) => p,
            Err(e) => {
                panic!("{:?}", e);
            }
        };
        println!("{}", res);
    }
    Ok(symbol_table)
}
