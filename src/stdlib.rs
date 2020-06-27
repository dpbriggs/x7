use crate::symbols::{Expr, Function, LispResult, ProgramError, SymbolTable};

macro_rules! exact_len {
    ($args:expr, $len:literal) => {
        if $args.len() != $len {
            return Err(ProgramError::WrongNumberOfArgs);
        }
    };
}

// ARITHMETIC

fn eq_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let all_eq = exprs.windows(2).all(|x| x[0] == x[1]);
    Ok(Expr::Bool(all_eq))
}

fn add_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc + &x)
}

fn sub_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc - &x)
}

fn mult_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc * &x)
}

fn div_exprs(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc / &x)
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

fn list(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs.into()))
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

// TODO: Conditionals
// fn cond(exprs: &[Expr]) -> LispResult<Expr> {
//     if exprs.len() % 2 != 0 {
//         return Err(ProgramError::CondBadConditionNotEven);
//     }
//     Ok(Expr::list(vec![]))
// }

// FUNC

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
    let mut sym_copy = symbol_table.clone();
    sym_copy.add(symbols.get_list()?.chunks_exact(2))?;
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
        ("/", 2, div_exprs, true),
        ("=", 1, eq_exprs, true),
        ("inc", 1, inc_exprs, true),
        // // MISC
        ("ident", 0, ident, true),
        ("quote", 0, quote, false),
        ("print", 1, print, true),
        ("println", 1, println, true),
        ("def", 1, def, false),
        // FUNC TOOLS
        ("map", 1, map, true),
        ("apply", 2, apply, true),
        ("reduce", 2, reduce, true),
        // Data Structures
        ("list", 0, list, true), // FUNDAMENTALS
        ("fn", 0, func, false),
        ("defn", 3, defn, false),
        ("bind", 2, bind, true)
    );
    // syms
    make_stdlib_consts!(
        syms,
        ("true", Expr::Bool(true)),
        ("false", Expr::Bool(false))
    )
}
