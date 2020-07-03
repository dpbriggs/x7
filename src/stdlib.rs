use crate::iterators::{LazyMap, NaturalNumbers, Take};
use crate::modules::load_x7_stdlib;
use crate::symbols::{Expr, Function, LispResult, Num, ProgramError, SymbolTable};
use bigdecimal::{BigDecimal, FromPrimitive, One, ToPrimitive};
use im::{vector, Vector};

macro_rules! num {
    ($n:expr) => {
        Expr::Num(BigDecimal::from_usize($n).unwrap())
    };
}

macro_rules! num_f {
    ($n:expr) => {
        Expr::Num(BigDecimal::from_f64($n).unwrap())
    };
}

macro_rules! exact_len {
    ($args:expr, $len:literal) => {
        if $args.len() != $len {
            return Err(ProgramError::WrongNumberOfArgs);
        }
    };
}

// ARITHMETIC

fn lt_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs.iter().skip(1).all(|e| first < e);
    Ok(Expr::Bool(rest))
}

fn lte_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs.iter().skip(1).all(|e| first <= e);
    Ok(Expr::Bool(rest))
}

fn gt_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs.iter().skip(1).all(|e| first > e);
    Ok(Expr::Bool(rest))
}

fn gte_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let rest = exprs.iter().skip(1).all(|e| first >= e);
    Ok(Expr::Bool(rest))
}

fn rem_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    exprs[0].clone() % &exprs[1]
}

fn or(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        if expr.get_bool()? {
            return Ok(Expr::Bool(true));
        }
    }
    Ok(Expr::Bool(false))
}

fn and(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs {
        if !expr.get_bool()? {
            return Ok(Expr::Bool(false));
        }
    }
    Ok(Expr::Bool(true))
}

fn not(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::Bool(!exprs[0].get_bool()?))
}

fn eq_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let first = &exprs[0];
    let all_eq = exprs.iter().all(|x| first == x);
    Ok(Expr::Bool(all_eq))
}

fn add_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs.iter().skip(1).try_fold(init, |acc, x| acc + x)
}

fn sub_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs.iter().skip(1).try_fold(init, |acc, x| acc - x)
}

fn mult_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs.iter().skip(1).try_fold(init, |acc, x| acc * x)
}

fn div_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    exprs.iter().skip(1).try_fold(init, |acc, x| acc / x)
}

fn inc_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() > 1 {
        Err(ProgramError::WrongNumberOfArgs)
    } else if let Expr::Num(n) = &exprs[0] {
        Ok(Expr::Num(n + bigdecimal::BigDecimal::one()))
    } else {
        Err(ProgramError::BadTypes)
    }
}

// MISC

fn ident(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs))
}

fn quote(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Quote(exprs))
}

fn apply(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    exprs[0].call_fn(exprs[1].get_list()?, symbol_table)
}

// fn inner_comp(exprs, es: Vector<Expr>, sym: &SymbolTable) -> LispResult<Expr> {
//     let mut res: Vector<Expr> = es;
//     for func in exprs.iter() {
//         res = match func.call_fn(res, sym) {
//             Ok(l) => match l.get_list() {
//                 Ok(li) => li,
//                 Err(e) => return Err(e),
//             },
//             Err(e) => return Err(e),
//         }
//     }
//     return Ok(Expr::List(res));
// }

// XXX: Closure lifetime resolution is some magic shit.
//      For some reason it compiles now no idea why  ¯\_(ツ)_/¯
// #[inline(always)]
// fn lifetimes_are_hard<F>(f: F) -> F
// where
//     F: for<'c> Fn(Vector<Expr>, &'c SymbolTable) -> LispResult<Expr> + Sync + Send,
// {
//     f
// }

fn comp<'c>(exprs: Vector<Expr>, _symbol_table: &'c SymbolTable) -> LispResult<Expr> {
    let compose = move |es, sym: &SymbolTable| {
        let mut res: Vector<Expr> = es;
        for func in exprs.iter() {
            res = match func.call_fn(res, sym) {
                Ok(l) => match l.get_list() {
                    Ok(li) => li,
                    Err(e) => return Err(e),
                },
                Err(e) => return Err(e),
            }
        }
        return Ok(Expr::List(res));
    };
    let f = Function::new("AnonCompFn".into(), 1, Arc::new(compose), true);
    Ok(Expr::Function(f))
}

fn def(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    symbol_table.add_local(&exprs[0], &exprs[1].eval(symbol_table)?)
}

fn exprs_do(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs.clone().slice(..exprs.len() - 1).iter() {
        if let Err(e) = expr.eval(symbol_table) {
            println!("{:?}", e);
        }
    }
    exprs[exprs.len() - 1].eval(symbol_table)
}

fn panic(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let msg = if let Expr::String(s) = &exprs[0] {
        s.to_string()
    } else {
        format!("{}", exprs[0])
    };
    panic!(msg);
}

// PRINT

fn print(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in &exprs {
        print!("{}", expr);
    }
    Ok(Expr::Num((exprs.len() as u64).into()))
}

fn println(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in &exprs {
        println!("{}", expr);
    }
    Ok(Expr::Num((exprs.len() as u64).into()))
}

fn type_of(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let ty = match &exprs[0] {
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
    };
    Ok(Expr::String(ty.into()))
}

// FUNC

fn cond(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() % 2 != 0 {
        return Err(ProgramError::CondBadConditionNotEven);
    }
    let mut iter = exprs.iter();
    while let Some(pred) = iter.next() {
        let body = iter.next().unwrap();
        if pred.eval(symbol_table)?.is_bool_true()? {
            return body.eval(symbol_table);
        }
    }
    Err(ProgramError::CondNoExecutionPath)
}

fn map(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    // TODO: Performance fix this entire thing
    exact_len!(exprs, 2);
    let f = &exprs[0];
    if let Ok(iter) = exprs[1].get_iterator() {
        return LazyMap::new(iter, f.get_function()?);
    }
    let mut l = exprs[1].get_list()?;
    for expr in l.iter_mut() {
        let old = expr.clone();
        *expr = f.call_fn(Vector::unit(old), symbol_table)?;
    }
    Ok(Expr::List(l))
}

// Like map, but doesn't produce a list.
fn foreach(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let f = &exprs[0];
    if let Ok(iter) = exprs[1].get_iterator() {
        while let Some(x) = iter.next(symbol_table) {
            f.call_fn(Vector::unit(x?), symbol_table)?;
        }
    } else if let Ok(list) = exprs[1].get_list() {
        for x in list.iter() {
            f.call_fn(Vector::unit(x.clone()), symbol_table)?;
        }
    } else {
        return Err(ProgramError::BadTypes);
    };
    Ok(Expr::Nil)
}

fn filter(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() == 1 {
        // TODO: Transducer case
        // return Transducer::new(|exprs, sym| filter(&exprs[0]))
        return Ok(Expr::Nil);
    }
    exact_len!(exprs, 2);
    let f = &exprs[0];
    let l = exprs[1].get_list()?;
    let mut res = Vector::new();
    for expr in l {
        if f.call_fn(Vector::unit(expr.clone()), symbol_table)?
            .get_bool()?
        {
            res.push_back(expr);
        }
    }
    Ok(Expr::List(res))
}

/// reduce
/// (f init coll)
fn reduce(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() != 2 && exprs.len() != 3 {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let (mut init, list) = if exprs.len() == 2 {
        let (mut head, tail) = exprs[1].get_list()?.split_at(1);
        (head.pop_front().ok_or(ProgramError::NotEnoughArgs)?, tail)
    } else {
        (exprs[1].clone(), exprs[2].get_list()?)
    };
    let f = &exprs[0];
    for item in list {
        init = f.call_fn(vector![init, item], symbol_table)?;
    }
    Ok(init)
}

fn bind(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    let symbols = &exprs[0];
    if !symbols.is_even_list() {
        return Err(ProgramError::WrongNumberOfArgs);
    }
    let sym_copy = symbol_table.clone();
    let list = symbols.get_list()?;
    let mut iter = list.iter();
    while let Some(l) = iter.next() {
        let r = iter.next().unwrap();
        sym_copy.add_local(l, &r.eval(&sym_copy)?)?;
    }
    exprs[1].eval(&sym_copy)
}

fn func(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let arg_symbols = exprs[0].get_list()?;
    let min_args = match arg_symbols.iter().position(|e| e.symbol_matches("&")) {
        Some(index) => index,
        None => arg_symbols.len(),
    };
    let body = exprs[1].clone();
    let f = Arc::new(move |_args: Vector<Expr>, sym: &SymbolTable| body.eval(sym));
    let f = Function::new_named_args(
        "AnonFn".to_string(),
        min_args,
        f,
        arg_symbols.iter().cloned().collect(),
        true,
    );
    Ok(Expr::Function(f))
}

fn defn(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    let name = &exprs[0];
    let func =
        func(exprs.clone().slice(1..), symbol_table)?.rename_function(name.get_symbol_string()?)?;
    def(vector![name.clone(), func.clone()], symbol_table)?;
    Ok(func)
}

// LISTS

fn list(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs))
}

fn tuple(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Tuple(exprs))
}

fn nth(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let index = exprs[0]
        .get_num()?
        .to_usize()
        .ok_or(ProgramError::BadTypes)?;
    exprs[1]
        .get_list()?
        .get(index)
        .cloned()
        .ok_or(ProgramError::BadTypes)
}

fn cons(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let mut list = exprs[1].get_list()?;
    list.push_front(exprs[0].clone());
    Ok(Expr::List(list))
}

fn head(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let list = exprs[0].get_list()?;
    if list.is_empty() {
        Ok(Expr::Nil)
    } else {
        Ok(list[0].clone())
    }
}

fn tail(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let mut list = exprs[0].get_list()?;
    if list.is_empty() {
        Ok(Expr::Nil)
    } else {
        Ok(Expr::List(list.slice(1..)))
    }
}

fn range(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.is_empty() {
        return NaturalNumbers::new();
    }
    exact_len!(exprs, 1);
    let num = exprs[0]
        .get_num()?
        .to_usize()
        .ok_or(ProgramError::Custom(format!(
            "Cannot have a negative range {}",
            exprs[0].get_num()?
        )))?;
    let list = (0..num)
        .map(|n| Expr::Num(BigDecimal::from_usize(n).unwrap()))
        .collect();
    Ok(Expr::List(list))
}

fn take(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let num = exprs[0].get_num()?.to_usize().unwrap();
    let iter = exprs[1].get_iterator()?;
    Take::new(num, iter)
}

fn doall(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    use crate::iterators::LazyIter;
    exprs[0].get_iterator()?.eval(symbol_table)
}

fn shuffle(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let mut list: Vec<_> = exprs[0].get_list()?.iter().cloned().collect();
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    list.shuffle(&mut thread_rng());
    Ok(Expr::List(list.into()))
}

macro_rules! num {
    ($n:expr) => {
        Expr::Num(BigDecimal::from_usize($n).unwrap())
    };
}

fn len(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(num!(exprs[0].get_list()?.len()))
    // Ok(Expr::Num(exprs[0].get_list()?.len() as Num))
}

fn sort(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let mut list = exprs[0].full_order_list()?;
    list.sort();
    Ok(Expr::List(list))
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
        ("panic", 1, panic, true),
        ("type", 1, type_of, true),
        // FUNC TOOLS
        ("map", 1, map, true),
        ("foreach", 2, foreach, true),
        ("filter", 1, filter, true),
        ("apply", 2, apply, true),
        ("do", 1, exprs_do, false),
        ("comp", 1, comp, true),
        ("reduce", 2, reduce, true),
        // Functions
        ("fn", 0, func, false),
        ("defn", 3, defn, false),
        ("bind", 2, bind, false),
        // Iterators
        ("take", 2, take, true),
        ("doall", 1, doall, true),
        // Lists
        ("list", 0, list, true),
        ("tuple", 0, tuple, true),
        ("nth", 2, nth, true),
        ("head", 1, head, true),
        ("tail", 1, tail, true),
        ("cons", 2, cons, true),
        ("range", 0, range, true),
        ("len", 1, len, true),
        ("sort", 1, sort, true)
    );
    load_x7_stdlib(&syms).unwrap();
    syms
}
