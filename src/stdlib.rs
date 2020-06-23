use crate::symbols::{DataType, Expr, Function, LispResult, ProgramError, SymbolTable};

// ARITHMETIC

fn add_exprs(exprs: &[Expr]) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc + x)
}

fn sub_exprs(exprs: &[Expr]) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc - x)
}

fn mult_exprs(exprs: &[Expr]) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc * x)
}

fn div_exprs(exprs: &[Expr]) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs[1..].iter().try_fold(init, |acc, x| acc / x)
}

fn inc_exprs(exprs: &[Expr]) -> LispResult<Expr> {
    if exprs.len() > 1 {
        Err(ProgramError::WrongNumberOfArgs)
    } else if let DataType::Num(n) = exprs[0].dataty {
        exprs[0].bind(DataType::Num(n + 1.0))
    } else {
        Err(ProgramError::BadTypes)
    }
}

// // MISC

fn ident(exprs: &[Expr]) -> LispResult<Expr> {
    Ok(Expr::list(exprs.into()))
}

fn quote(exprs: &[Expr]) -> LispResult<Expr> {
    dbg!(exprs);
    Ok(Expr::quote(exprs.into()))
}

fn list(exprs: &[Expr]) -> LispResult<Expr> {
    Ok(Expr::list(exprs.into()))
}

fn apply(exprs: &[Expr]) -> LispResult<Expr> {
    dbg!(exprs);
    let mut new_expr = Vec::new();
    new_expr.push(exprs[0].clone());
    new_expr.append(&mut exprs[1].list_iter()?);
    dbg!(&new_expr);
    Expr::list(new_expr).eval()
}

// // PRINT

fn print(exprs: &[Expr]) -> LispResult<Expr> {
    for expr in exprs {
        print!("{}", expr);
    }
    Ok(Expr::new(DataType::Num(exprs.len() as f64)))
}

fn println(exprs: &[Expr]) -> LispResult<Expr> {
    for expr in exprs {
        println!("{}", expr);
    }
    Ok(Expr::new(DataType::Num(exprs.len() as f64)))
}

// fn cond(exprs: &[Expr]) -> LispResult<Expr> {
//     if exprs.len() % 2 != 0 {
//         return Err(ProgramError::CondBadConditionNotEven);
//     }
//     Ok(Expr::list(vec![]))
// }

// FUNC

fn map(exprs: &[Expr]) -> LispResult<Expr> {
    // TODO: Performance fix this entire thing
    dbg!(exprs);
    if exprs.len() != 2 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let f = &exprs[0];
    let list = exprs[1].list_iter()?;
    let mut res = Vec::with_capacity(list.len());
    for expr in list {
        res.push(f.call_fn(&[expr])?);
    }
    Ok(Expr::list(res))
}

/// reduce
/// (f [init] coll)
fn reduce(exprs: &[Expr]) -> LispResult<Expr> {
    dbg!(exprs.len());
    if exprs.len() != 2 && exprs.len() != 3 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let f = &exprs[0];
    let mut init = exprs[1].clone();
    for item in exprs[2].dataty.coll_iter()? {
        init = f.call_fn(&[init, item.clone()])?;
    }
    Ok(init)
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
            let mut syms = SymbolTable::new();
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
        ("apply", 2, apply),
        ("reduce", 2, reduce),
        // Data Structures
        ("list", 0, list) // FUNDAMENTALS
                          // ("fn", 0, func)
    );
    syms
}
