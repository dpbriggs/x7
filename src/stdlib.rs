use crate::symbols::{Expr, Function, LispResult, ProgramError, SymbolTable};

// ARITHMETIC

fn add_exprs(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone().eval(symbol_table)?;
    exprs[1..]
        .iter()
        .try_fold(init, |acc, x| acc + &x.eval(symbol_table)?)
}

fn sub_exprs(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone().eval(symbol_table)?;
    exprs[1..]
        .iter()
        .try_fold(init, |acc, x| acc - &x.eval(symbol_table)?)
}

fn mult_exprs(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone().eval(symbol_table)?;
    exprs[1..]
        .iter()
        .try_fold(init, |acc, x| acc * &x.eval(symbol_table)?)
}

fn div_exprs(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone().eval(symbol_table)?;
    exprs[1..]
        .iter()
        .try_fold(init, |acc, x| acc / &x.eval(symbol_table)?)
}

fn inc_exprs(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() > 1 {
        Err(ProgramError::WrongNumberOfArgs)
    } else if let Expr::Num(n) = exprs[0].eval(symbol_table)? {
        Ok(Expr::Num(n + 1.0))
    } else {
        Err(ProgramError::BadTypes)
    }
}

// // MISC

fn ident(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs.into()))
}

fn quote(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Quote(exprs.into()))
}

fn list(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    let constituents: Result<_, _> = exprs.iter().map(|e| e.eval(symbol_table)).collect();
    Ok(Expr::List(constituents?))
}

// fn apply(exprs: &[Expr]) -> LispResult<Expr> {
//     dbg!(exprs);
//     let mut new_expr = Vec::new();
//     new_expr.push(exprs[0].clone());
//     new_expr.append(&mut exprs[1].list_iter()?);
//     dbg!(&new_expr);
//     Expr::List(new_expr).eval()
// }

// // PRINT

fn print(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs.iter().map(|e| e.eval(symbol_table)) {
        print!("{}", expr?);
    }
    Ok(Expr::Num(exprs.len() as f64))
}

fn println(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs.iter().map(|e| e.eval(symbol_table)) {
        println!("{}", expr?);
    }
    Ok(Expr::Num(exprs.len() as f64))
}

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
    let f = &exprs[0].eval(symbol_table)?;
    let mut res = Vec::with_capacity(exprs.len() - 1);
    // dbg!(&exprs[1]);
    for expr in exprs[1].eval_iter(symbol_table, 1)? {
        dbg!(&f);
        dbg!(&expr);
        res.push(f.call_fn(&[expr?], symbol_table)?);
    }
    Ok(Expr::List(res))
}

/// reduce
/// (f [init] coll)
fn reduce(exprs: &[Expr], symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 && exprs.len() != 3 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let f = &exprs[0].eval(symbol_table)?;
    let mut init = exprs[1].eval(symbol_table)?;
    for item in exprs[2].eval(symbol_table)?.eval_iter(symbol_table, 0)? {
        init = f.call_fn(&[init, item?], symbol_table)?;
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
    // Ok(Expr::Nil)
}

fn func(exprs: &[Expr], _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let arg_symbols = exprs[0].get_list()?;
    let min_args = match arg_symbols.iter().position(|e| e.symbol_matches("&")) {
        Some(index) => index,
        None => arg_symbols.len(),
    };
    dbg!(min_args);
    let body = exprs[1].clone();
    let f = Arc::new(move |_args: &[Expr], sym: &SymbolTable| body.eval(sym));
    let f = Function::new_named_args("AnonFn".to_string(), min_args, f, arg_symbols.to_vec());
    Ok(Expr::Function(f))
}

// TODO: Figure this out
// fn func(exprs: &[Expr]) -> LispResult<Expr> {
//     // let symbol = exprs[0].clone();
//     let symbol = match exprs[0].dataty {
//         DataType::Symbol(s) => s.clone(),
//         _ => return Err(ProgramError::BadTypes),
//     };
//     let args = exprs[1].clone();
//     let body = exprs[2].clone();
//     let func_body = Arc::new(|e: &[Expr]| Ok(Expr::list(exprs.to_vec())));
//     let f = Function::new(symbol, 0, func_body);

//     Ok(Expr::func(f))
// }

use std::sync::Arc;

macro_rules! make_stdlib_fns {
	  ( $(($sym:literal, $minargs:expr, $func:ident)),* ) => {
        {
            let syms = SymbolTable::new();
            $(
		            syms.add_global_fn(Function::new($sym.into(), $minargs, Arc::new($func)));
            )*
            syms
        }
	  };
}

#[allow(clippy::let_and_return)]
pub(crate) fn create_stdlib_symbol_table() -> SymbolTable {
    let syms = make_stdlib_fns!(
        // ARITHMETIC
        ("+", 1, add_exprs),
        ("-", 1, sub_exprs),
        ("*", 1, mult_exprs),
        ("/", 2, div_exprs),
        ("inc", 1, inc_exprs),
        // // MISC
        ("ident", 0, ident),
        ("quote", 0, quote),
        ("print", 1, print),
        ("println", 1, println),
        // FUNC TOOLS
        ("map", 1, map),
        // ("apply", 2, apply),
        ("reduce", 2, reduce),
        // Data Structures
        ("list", 0, list), // FUNDAMENTALS
        ("fn", 0, func),
        ("bind", 2, bind)
    );
    syms
}
