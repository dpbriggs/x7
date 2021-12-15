#![allow(clippy::unnecessary_wraps)]
use crate::interner::InternedString;
use crate::iterators::{
    CartesianProduct, LazyList, LazyMap, NaturalNumbers, Skip, Take, TakeWhile,
};
use crate::modules::load_x7_stdlib;
use crate::records::RecordDoc;
use crate::records::{DynRecord, FileRecord, RegexRecord};
use crate::symbols::{Expr, Function, LispResult, ProgramError, SymbolTable};
use crate::{bad_types, iterators::LazyFilter};
use crate::{cli::Options, iterators::IterType};
use anyhow::{anyhow, bail, ensure, Context};
use bigdecimal::{BigDecimal, FromPrimitive, One, ToPrimitive};
use im::{vector, Vector};
use itertools::Itertools;

/// Macro to check if we have the right number of args,
/// and throw a nice error if we don't.
#[macro_export]
macro_rules! exact_len {
    ($args:expr, $len:literal) => {
        use anyhow::ensure;
        use crate::symbols::ProgramError;
        ensure!($args.len() == $len, ProgramError::WrongNumberOfArgs($len))
    };
    ($args:expr, $($len:literal),*) => {
        {
            let mut is_ok_len = false;
            $(
                is_ok_len = is_ok_len || $args.len() == $len;
            )*
                if !is_ok_len {
                    let mut expected_args = String::new();
                    $(
                        expected_args.push_str(&format!("{} ", $len));
                    )*
                    bail!(anyhow!(format!("Wrong number of args! Expected {}, but received {}", expected_args, $args.len())));
                }
        }
    };

}

// ARITHMETIC

// TODO: Check if the types make sense to compare. (i.e. ordering, etc)

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

fn xor(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if !exprs.is_empty() {
        let mut res = exprs[0].get_bool()?;
        for b in exprs.iter().skip(1) {
            res ^= b.get_bool()?;
        }
        Ok(Expr::Bool(res))
    } else {
        Ok(Expr::Bool(true))
    }
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
    let mut init = exprs[0].clone();
    for e in exprs.iter().skip(1) {
        init = (init + e)?;
    }
    // TODO: Figure out why this is slightly slower
    // exprs.iter().skip(1).try_fold(init, |acc, x| acc + x)

    Ok(init)
}

fn sub_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let init = exprs[0].clone();
    if exprs.len() == 1 {
        return Ok(Expr::num(BigDecimal::from(-1) * init.get_num()?));
    }
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
    exact_len!(exprs, 1);
    let res = match exprs[0].clone() {
        Expr::Integer(i) => Expr::Integer(i + 1), // TODO: Handle overflow
        Expr::Num(n) => Expr::num(n + bigdecimal::BigDecimal::one()),
        otherwise => return bad_types!("num or int", otherwise),
    };
    Ok(res)
}

fn dec_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let res = match exprs[0].clone() {
        Expr::Integer(i) => Expr::Integer(i - 1), // TODO: Handle overflow
        Expr::Num(n) => Expr::num(n - bigdecimal::BigDecimal::one()),
        otherwise => return bad_types!("num or int", otherwise),
    };
    Ok(res)
}

fn sqrt_exprs(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let num_f64 = match &exprs[0] {
        Expr::Integer(i) => *i as f64,
        Expr::Num(i) => {
            if let Some(f) = i.to_f64() {
                f
            } else {
                return i
                    .sqrt()
                    .map(Expr::num)
                    .ok_or_else(|| anyhow!("Cannot square root a negative number!"));
            }
        }
        otherwise => return bad_types!("num or int", otherwise),
    };
    Ok(Expr::num(BigDecimal::from_f64(num_f64.sqrt()).unwrap()))
}

fn pow(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let base = exprs[0].get_num()?;
    let exp = exprs[1].get_num()?.round(0).to_u32().unwrap(); // TODO: Handle error
    if exp == 0 {
        return Ok(Expr::num(BigDecimal::one()));
    }
    let mut res = base.clone();
    for _ in 0..(exp - 1) {
        res *= &base;
    }
    Ok(Expr::num(res))
}

fn int(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(s) = exprs[0].get_string() {
        let res: u64 = s
            .parse()
            .map_err(|_| anyhow!("Could not convert to an int."))?;
        return Ok(Expr::num(res));
    }
    let res = match &exprs[0] {
        Expr::Integer(i) => Expr::Integer(*i),
        Expr::Num(i) => Expr::num(i.round(0)),
        otherwise => return bad_types!("num", otherwise),
    };
    Ok(res)
}

fn floor(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let n = exprs[0]
        .get_num()?
        .to_f64()
        .unwrap()
        .trunc()
        .to_u64()
        .unwrap(); // jesus
    Ok(Expr::num(BigDecimal::from(n)))
}

// MISC

fn ident(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(exprs[0].clone())
}

fn ident_exists(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let iden = exprs[0].get_symbol()?;
    Ok(Expr::Bool(symbol_table.symbol_exists(&iden)))
}

fn quote(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Quote(exprs))
}

fn symbol(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(s) = exprs[0].get_string() {
        Ok(Expr::Symbol(s.into()))
    } else {
        bad_types!("string", exprs[0])
    }
}

fn string(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(s) = exprs[0].get_string() {
        Ok(Expr::String(s))
    } else {
        Ok(Expr::String(format!("{}", &exprs[0])))
    }
}

fn eval(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    exprs[0].eval(symbol_table)
}

fn apply(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    exprs[0].call_fn(exprs[1].get_list()?, symbol_table)
}

fn err(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let msg = exprs.iter().join("");
    Err(anyhow!(msg))
}

fn all_symbols(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 0);
    let all_syms = symbol_table.get_canonical_doc_order();
    Ok(Expr::List(
        all_syms
            .into_iter()
            .map(|e| Expr::Symbol(e.into()))
            .collect(),
    ))
}

fn include(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let file_path = exprs[0].get_string()?;
    symbol_table.load_file(file_path)
}

fn doc(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    // TODO: Make records nice (merge Record and RecordDoc?)
    let sym = exprs[0].get_symbol_string()?;
    if let Some(doc) = symbol_table.get_doc_item(&sym.to_string()) {
        return Ok(Expr::String(doc));
    }

    let sym_eval = exprs[0].eval(symbol_table)?;
    if let Ok(f) = sym_eval.get_function() {
        if let Some(doc) = symbol_table.get_doc_item(&f.symbol.to_string()) {
            return Ok(Expr::String(doc));
        }
    }

    // Last ditch effort: eval it
    let doc = symbol_table
        .get_doc_item(&sym_eval.get_symbol_string()?.to_string())
        .unwrap_or_else(|| format!("No documentation for {}", sym));
    Ok(Expr::String(doc))
}

fn inline_transform(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let data = exprs[0].get_list()?;
    let functions = exprs[1].get_list()?;

    Ok(Expr::Tuple(
        functions
            .iter()
            .zip(data)
            .map(|(f, x)| f.call_fn(im::Vector::unit(x), symbol_table))
            .collect::<LispResult<Vector<Expr>>>()?,
    ))
}

// XXX: Closure lifetime resolution is some magic shit.
//      For some reason it compiles now no idea why  ¯\_(ツ)_/¯
// #[inline(always)]
// fn lifetimes_are_hard<F>(f: F) -> F
// where
//     F: for<'c> Fn(Vector<Expr>, &'c SymbolTable) -> LispResult<Expr> + Sync + Send,
// {
//     f
// }

// TODO: Make this work.
fn comp(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let compose = move |es, sym: &SymbolTable| {
        let mut res: Vector<Expr> = es;
        for func in exprs.iter().rev() {
            let fn_call = func.call_fn(res, sym);
            res = match fn_call {
                Ok(e) => Vector::unit(e),
                // Ok(l) => match l.get_list() {
                //     Ok(li) => li,
                //     Err(e) => return Err(e),
                // },
                Err(e) => return Err(e),
            }
        }
        Ok(Expr::List(res))
    };
    let f = Function::new("AnonCompFn".into(), 1, Arc::new(compose), true);
    Ok(Expr::function(f))
}

fn def(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    symbol_table.add_local(&exprs[0], &exprs[1].eval(symbol_table)?)?;
    Ok(Expr::Nil)
}

fn exprs_do(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in exprs.clone().slice(..exprs.len() - 1).iter() {
        expr.eval(symbol_table)?;
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
    panic!("{}", msg);
}

fn sleep(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let dur = exprs[0]
        .get_num()?
        .to_u64()
        .ok_or_else(|| anyhow!("Failed to convert {} to u64", exprs[0]))?;
    std::thread::sleep(Duration::from_secs(dur));
    Ok(Expr::Nil)
}

// PRINT

fn print(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    for expr in &exprs {
        print!("{}", expr);
    }
    Ok(Expr::num(exprs.len()))
}

fn println(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let item = exprs.iter().join("");
    println!("{}", item);
    Ok(Expr::Nil)
}

fn type_of(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::String(exprs[0].get_type_str().into()))
}

// FUNC

fn cond(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    ensure!(exprs.len() % 2 == 0, ProgramError::CondBadConditionNotEven);
    let mut iter = exprs.iter();
    while let Some(pred) = iter.next() {
        let body = iter.next().unwrap();
        if pred.eval(symbol_table)?.is_bool_true()? {
            return body.eval(symbol_table);
        }
    }
    bail!(ProgramError::CondNoExecutionPath)
}

fn expr_match(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    let item = exprs[0].eval(symbol_table)?;
    let mut iter = exprs.iter().skip(1);
    ensure!(
        (exprs.len() - 1) % 2 == 0,
        anyhow!("Match requires an even list of then")
    );
    while let Some(lhs) = iter.next() {
        let then = iter.next().unwrap();
        if lhs.is_symbol_underscore() {
            return then.eval(symbol_table);
        }
        let lhs = lhs.eval(symbol_table)?;
        if lhs == item {
            return then.eval(symbol_table);
        }
    }
    bail!(anyhow!("No execution paths for match!"))
}

fn if_gate(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    if exprs[0].eval(symbol_table)?.get_bool()? {
        exprs[1].eval(symbol_table)
    } else {
        exprs[2].eval(symbol_table)
    }
}

fn map(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let f = &exprs[0];
    if let Ok(iter) = exprs[1].get_iterator() {
        return LazyMap::lisp_res(iter, f.get_function()?.clone());
    }
    let mut l = exprs[1].get_list()?;
    for expr in l.iter_mut() {
        let old = expr.clone();
        *expr = f.call_fn(Vector::unit(old), symbol_table)?;
    }
    Ok(Expr::Tuple(l))
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
        bail!(ProgramError::BadTypes)
    };
    Ok(Expr::Nil)
}

fn filter(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.len() == 1 {
        // TODO: Transducer case
        // return Transducer::new(|exprs, sym| filter(&exprs[0]))
        todo!()
    }
    exact_len!(exprs, 2);
    let f = &exprs[0];
    if let Ok(iter) = exprs[1].get_iterator() {
        return LazyFilter::lisp_res(iter, f.get_function()?.clone());
    }
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

fn reduce_iterator(
    f: &Expr,
    init: Option<Expr>,
    tail: IterType,
    symbol_table: &SymbolTable,
) -> LispResult<Expr> {
    let mut init = match init {
        Some(e) => e,
        None => tail.next(symbol_table).ok_or_else(|| {
            anyhow!("Attempted to reduce without initial argument using an empty list")
        })??,
    };
    while let Some(next) = tail.next(symbol_table) {
        init = f.call_fn(vector![init, next?], symbol_table)?;
    }
    Ok(init)
}

/// reduce
/// (f init coll)
fn reduce(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2, 3);
    let f = &exprs[0];
    let (mut init, list) = if exprs.len() == 2 {
        if exprs[1].is_iterator() {
            let iter = exprs[1].get_iterator()?;
            return reduce_iterator(f, None, iter, symbol_table);
        }
        let mut list = exprs[1].get_list()?;
        ensure!(
            !list.is_empty(),
            "Attempted to reduce without initial argument using an empty list"
        );
        let head = list.pop_front().unwrap();
        (head, list)
    } else {
        if exprs[2].is_iterator() {
            let iter = exprs[2].get_iterator()?;
            return reduce_iterator(f, Some(exprs[1].clone()), iter, symbol_table);
        }
        (exprs[1].clone(), exprs[2].get_list()?)
    };
    for item in list {
        init = f.call_fn(vector![init, item], symbol_table)?;
    }
    Ok(init)
}

fn any(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let pred = exprs[0].get_function()?;
    let body = &exprs[1].get_list()?;
    for b in body.iter().cloned() {
        if pred
            .call_fn(im::Vector::unit(b), symbol_table)?
            .get_bool()?
        {
            return Ok(Expr::Bool(true));
        }
    }
    Ok(Expr::Bool(false))
}

fn all(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let pred = exprs[0].get_function()?;
    let body = &exprs[1].get_list()?;
    for b in body.iter().cloned() {
        if !pred
            .call_fn(im::Vector::unit(b), symbol_table)?
            .get_bool()?
        {
            return Ok(Expr::Bool(false));
        }
    }
    Ok(Expr::Bool(true))
}

fn skip(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let skips_left = exprs[0].get_usize()?;
    let inner = exprs[1].get_iterator()?;
    Skip::lisp_res(skips_left, inner)
}

fn lazy(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(list) = exprs[0].get_list() {
        return LazyList::lisp_new(list);
    }
    // let iter = match &exprs[0] {
    //     Expr::LazyIter(iter) => iter.clone(),
    //     _ => return bad_types!("iter", &exprs[0]),
    // };
    // Ok(Expr::LazyIter(iter))
    Ok(Expr::Nil)
}

fn bind(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    let symbols = &exprs[0];
    let sym_copy = symbol_table.clone();
    let list = symbols.get_list()?;
    ensure!(
        list.len() % 2 == 0,
        anyhow!("Error: bind requires an even list of expressions, but was given a list of length {}. List given was: {}", list.len(), symbols)
    );

    let mut iter = list.iter();
    while let Some(l) = iter.next() {
        let r = iter.next().unwrap();
        sym_copy.add_local(l, &r.eval(&sym_copy)?)?;
    }
    exprs[1].eval(&sym_copy)
}

fn make_func(
    exprs: Vector<Expr>,
    symbol_table: &SymbolTable,
    name: InternedString,
) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let arg_symbols = exprs[0].get_list()?;
    let min_args = match arg_symbols.iter().position(|e| e.symbol_matches("&")) {
        Some(index) => index,
        None => arg_symbols.len(),
    };
    let body = exprs[1].clone();
    let f = Arc::new(move |_args: Vector<Expr>, sym: &SymbolTable| body.eval(sym));
    let f = Function::new_named_args(
        name,
        min_args,
        f,
        arg_symbols
            .iter()
            .map(|e| e.get_symbol_string())
            .try_collect()?,
        true,
        symbol_table
            .get_func_locals()
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect(),
    )?;
    Ok(Expr::function(f))
}

fn func(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    make_func(exprs, symbol_table, "AnonFn".into())
}

fn defn(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3, 4);
    let (name, doc, args, body) = if exprs.len() == 3 {
        (exprs[0].clone(), None, exprs[1].clone(), exprs[2].clone())
    } else {
        (
            exprs[0].clone(),
            Some(exprs[1].eval(symbol_table)?.get_string()?),
            exprs[2].clone(),
            exprs[3].clone(),
        )
    };

    let sym_name = name.get_symbol_string()?;

    // Make a function
    let func = make_func(vector![args, body], symbol_table, sym_name)?;

    // Add the function to the symbol table
    def(vector![name, func.clone()], symbol_table)?;

    // If given docs, add it to the symbol table
    if let Some(doc) = doc {
        symbol_table.add_doc_item(sym_name.to_string(), doc);
    }

    // return the function
    Ok(func)
}

// TODO: Find a nicer name for this
fn anon_fn_sugar(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let body = exprs[0].clone();
    let f = Arc::new(move |args: Vector<Expr>, sym: &SymbolTable| {
        let sym_args: Vec<_> = (1..args.len() + 1)
            .map(|i| format!("${}", i).into())
            .collect();
        let new_sym = sym.with_locals(&sym_args, None, args);
        body.eval(&new_sym)
    });
    let f = Function::new("AnonFn".into(), 0, f, true);
    Ok(Expr::Function(Arc::new(f)))
}

// Dict

fn make_dict(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    ensure!(
        exprs.len() % 2 == 0,
        "Error: dict requires an even list of arguments."
    );
    let mut dict = im::HashMap::new();
    for (key, value) in exprs.iter().tuples() {
        dict.insert(key.clone(), value.clone());
    }
    Ok(Expr::Dict(dict))
}

fn assoc(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let mut dict = exprs[0].get_dict()?;
    for (key, value) in exprs.iter().skip(1).tuples() {
        dict.insert(key.clone(), value.clone());
    }
    Ok(Expr::Dict(dict))
}

fn remove(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let mut dict = exprs[0].get_dict()?;
    for key in exprs.iter().skip(1) {
        dict.remove(key);
    }
    Ok(Expr::Dict(dict))
}

fn get_dict(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let dict = exprs[0].get_dict()?;
    let res = dict.get(&exprs[1]).cloned().unwrap_or(Expr::Nil);
    Ok(res)
}

fn set_dict(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    let mut dict = exprs[0].get_dict()?;
    let key = exprs[1].clone();
    let value = exprs[2].clone();
    dict.insert(key, value);
    Ok(Expr::Dict(dict))
}

fn values(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let dict = exprs[0].get_dict()?;
    Ok(Expr::Tuple(dict.values().cloned().collect()))
}

fn time(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let start = Instant::now();
    let _ = exprs[0].eval(symbol_table)?;
    let end = start.elapsed().as_millis() as u64;
    Ok(Expr::num(end))
}

// LISTS

fn list(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::List(exprs))
}

fn tuple(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    Ok(Expr::Tuple(exprs))
}

fn nth(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let index = exprs[0].get_usize()?;
    if let Ok(string) = exprs[1].get_string() {
        Ok(string
            .chars()
            .nth(index)
            .map(|c| Expr::String(c.into()))
            .unwrap_or(Expr::Nil))
    } else {
        let list = exprs[1].get_list()?;
        list.get(index).cloned().ok_or_else(|| {
            anyhow::anyhow!(
                "Failed to nth as list has length {} but attempted to index {}",
                list.len(),
                index
            )
        })
    }
}

fn flatten(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let l = exprs[0].get_list()?;
    let mut res = Vector::new();
    for item in l {
        match item {
            Expr::List(l) | Expr::Tuple(l) | Expr::Quote(l) => {
                l.into_iter().for_each(|i| res.push_back(i));
            }
            otherwise => res.push_back(otherwise),
        }
    }
    Ok(Expr::Tuple(res))
}

fn chars(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::Tuple(
        exprs[0]
            .get_string()?
            .chars()
            .map(|c| Expr::String(c.into()))
            .collect(),
    ))
}

fn split(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let split_by = exprs[0].get_string()?;
    let string = exprs[1].get_string()?;
    Ok(Expr::Tuple(
        string
            .split(&split_by)
            .map(|substr| Expr::String(substr.into()))
            .collect(),
    ))
}

fn replace(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    let from = exprs[0].get_string()?;
    let to = exprs[1].get_string()?;
    let string = exprs[2].get_string()?;
    Ok(Expr::String(string.replace(&from, &to)))
}

fn cons(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    exprs[1].push_front(exprs[0].clone())
}

fn head(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(list) = exprs[0].get_list() {
        if list.is_empty() {
            return Ok(Expr::Nil);
        } else {
            return Ok(list[0].clone());
        }
    }
    let string = exprs[0].get_string()?;
    if string.is_empty() {
        Ok(Expr::Nil)
    } else {
        let first_char = match string.chars().next() {
            Some(c) => c.to_string(),
            None => "".to_string(),
        };
        Ok(Expr::String(first_char))
    }
}

fn tail(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    if let Ok(mut list) = exprs[0].get_list() {
        if list.is_empty() {
            return Ok(Expr::Nil);
        } else {
            return Ok(Expr::List(list.slice(1..)));
        }
    }
    let string = exprs[0].get_string()?;
    if string.is_empty() {
        Ok(Expr::Nil)
    } else {
        let rest = string.chars().skip(1).collect();
        Ok(Expr::String(rest))
    }
}

fn zip(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let l_iter = exprs[0].get_list()?;
    let r_iter = exprs[1].get_list()?;
    Ok(Expr::List(
        l_iter
            .into_iter()
            .zip(r_iter)
            .map(|(l, r)| Expr::Tuple(vector![l, r]))
            .collect(),
    ))
}

fn rev(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    // TODO: Any number of args.
    exact_len!(exprs, 1);
    if let Ok(list) = exprs[0].get_list() {
        return Ok(Expr::List(list.into_iter().rev().collect()));
    }
    if let Ok(s) = &exprs[0].get_string() {
        return Ok(Expr::String(s.chars().rev().collect()));
    }
    bad_types!("string or list/quote/tuple", &exprs[0])
}

fn range(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    if exprs.is_empty() {
        return NaturalNumbers::lisp_res(None, None);
    }
    // TODO: Always lazy calculate range, or add a new function for it.
    exact_len!(exprs, 1, 2);
    let (mut start, end) = if exprs.len() == 1 {
        use bigdecimal::Zero;
        (BigDecimal::zero(), exprs[0].get_num()?)
    } else {
        (exprs[0].get_num()?, exprs[1].get_num()?)
    };
    match (start.to_i64(), end.to_i64()) {
        // fast path
        (Some(start), Some(end)) => Ok(Expr::Tuple((start..end).map(Expr::num).collect())),
        _ => {
            let mut ret = Vector::new();
            while start < end {
                ret.push_back(Expr::num(start.clone()));
                start += BigDecimal::one();
            }
            Ok(Expr::Tuple(ret))
        }
    }
}

fn take(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let num = exprs[0].get_usize()?;
    if let Ok(list) = exprs[1].get_list() {
        if num >= list.len() {
            return Ok(Expr::List(list));
        }
        let mut list = list;
        list.split_off(num);
        return Ok(Expr::List(list));
    }
    let iter = exprs[1].get_iterator()?;
    Take::lisp_res(num, iter)
}

fn take_while(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let pred = exprs[0].get_function()?;
    if let Ok(list) = exprs[1].get_list() {
        let mut new_list = Vector::new();
        for value in list.into_iter() {
            if !pred
                .call_fn(Vector::unit(value.clone()), symbol_table)?
                .get_bool()?
            {
                return Ok(Expr::List(new_list));
            }
            new_list.push_back(value);
        }
        return Ok(Expr::List(new_list));
    }
    let iter = exprs[1].get_iterator()?;
    TakeWhile::lisp_res(pred.clone(), iter)
}

fn find(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let pred = exprs[0].get_function()?;
    let iter = exprs[1].get_iterator()?; // todo handle other iterable types
    while let Some(item) = iter.next(symbol_table) {
        let item = item?;
        if pred
            .call_fn(Vector::unit(item.clone()), symbol_table)?
            .get_bool()?
        {
            return Ok(item);
        }
    }
    Ok(Expr::Nil)
}

fn slice(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 3);
    let lower = exprs[0].get_usize()?;
    let upper = exprs[1].get_usize()?;
    let mut list = {
        if let Ok(s) = exprs[2].get_string() {
            return Ok(Expr::String(s[lower..upper].to_string()));
        } else {
            exprs[2].get_list()?
        }
    };
    if lower >= list.len() {
        return Ok(Expr::Tuple(Vector::new()));
    }
    if upper < list.len() {
        let (left, _) = list.split_at(upper);
        list = left;
    }
    list = list.split_off(lower);
    Ok(Expr::Tuple(list))
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

fn random_bool(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 0);
    let b: bool = rand::random();
    Ok(Expr::Bool(b))
}

fn random_int(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2);
    let lower = exprs[0].get_num()?;
    let lower = lower
        .to_usize()
        .ok_or_else(|| anyhow!("Failed to convert {} to a usize!", &lower))?;
    let upper = exprs[1].get_num()?;
    let upper = upper
        .to_usize()
        .ok_or_else(|| anyhow!("Failed to convert {} to a usize!", &upper))?;
    let b: usize = rand::random::<usize>() % upper + lower;
    Ok(Expr::num(b))
}

fn primes(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let num = exprs[0].get_num()?;
    let less_than: u32 = num
        .to_u32()
        .ok_or_else(|| anyhow!("Could not fit {} into a u32!", num))?;
    let mut seen = vec![2];
    for n in (3..less_than).step_by(2) {
        if !seen.iter().any(|e| n % e == 0) {
            seen.push(n);
        }
    }
    Ok(Expr::List(seen.iter().map(|&i| Expr::num(i)).collect()))
}

fn divisors(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let num = exprs[0].get_int()?;
    let mut res = Vector::new();
    for i in 1..=num {
        if num % i == 0 {
            res.push_back(Expr::Integer(i));
        }
    }
    Ok(Expr::Tuple(res))
}

// Records

fn call_method(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    let rec = exprs[0].get_record()?;
    let method = &exprs[1].get_string()?;
    let args = exprs.clone().slice(2..);
    use crate::records::Record;
    rec.call_method(method, args, symbol_table)
}

fn doc_methods(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let sym: Cow<str> = match &exprs[0] {
        Expr::Symbol(s) => Cow::Owned(s.to_string()),
        Expr::Record(r) => r.type_name().into(),
        otherwise => return bad_types!("Symbol or Record", otherwise),
    };
    let docs = symbol_table
        .get_doc_methods(&sym)
        .into_iter()
        .map(|(doc, method)| Expr::Tuple(vector![Expr::String(doc), Expr::String(method)]))
        .collect();
    Ok(Expr::List(docs))
}

fn len(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    Ok(Expr::num(exprs[0].len()?))
}

fn sort(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 1);
    let mut list = exprs[0].full_order_list()?;
    list.sort();
    Ok(Expr::List(list))
}

fn distinct(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
    let sorted = sort(exprs, _symbol_table)?.get_list().unwrap();
    let mut v: Vec<_> = sorted.into_iter().collect();
    v.dedup();
    Ok(Expr::List(v.drain(..).collect()))
}

fn max_by(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
    exact_len!(exprs, 2); // TODO: Allow init arg
    let max_by_fn = exprs[0].get_function()?;
    let collection = &exprs[1].get_iterator()?;

    let mut curr_max = match collection.next(symbol_table) {
        Some(res) => res?,
        None => bail!("max-by called on an empty collection!"),
    };

    let mut curr_max_f = max_by_fn.call_fn(Vector::unit(curr_max.clone()), symbol_table)?;

    while let Some(item) = collection.next(symbol_table) {
        let item = item?;
        let item_f = max_by_fn.call_fn(Vector::unit(item.clone()), symbol_table)?;
        if item_f > curr_max_f {
            curr_max = item;
            curr_max_f = item_f;
        }
    }

    Ok(curr_max)
}

use std::borrow::Cow;
use std::time::Duration;
use std::{sync::Arc, time::Instant};

macro_rules! make_stdlib_fns {
    ( $(($sym:literal, $minargs:expr, $func:expr, $eval_args:expr, $doc:literal)),* ) => {
        {
            let mut globals = Vec::new();
            let mut docs = Vec::new();
            $(
                let f = Function::new($sym.into(), $minargs, Arc::new($func), $eval_args);
                globals.push(($sym.into(), Expr::function(f)));
                docs.push(($sym.into(), $doc.into()));
            )*
            SymbolTable::with_globals(globals, docs)
        }
    };
}

macro_rules! document_records {
    ($sym:expr, $($rec:ident),*) => {
        $(
            // Document the record itself.
            $sym.add_doc_item($rec::name().into(), $rec::type_doc().into());
            for (method, method_doc) in $rec::method_doc() {
                $sym.add_doc_item(format!("{}.{}", $rec::name(), method), (*method_doc).into());
            }
        )*
    };
}

pub fn create_stdlib_symbol_table_no_cli() -> SymbolTable {
    let opt = Options {
        // We haven't solved the $X7_PATH issue - i.e. where does
        // the x7 stdlib on the filesystem?
        do_not_load_native_stdlib: true,
        ..Default::default()
    };
    create_stdlib_symbol_table(&opt)
}

#[allow(clippy::let_and_return)]
pub fn create_stdlib_symbol_table(opts: &Options) -> SymbolTable {
    let syms = make_stdlib_fns!(
        // ARITHMETIC
        (
            "+",
            1,
            add_exprs,
            true,
            "Add two items together. Concatenates strings, lists, and tuples.
Example: (+ 1 1 1) ; 3
Example: (+ \"Hello \" \"World\") ; \"Hello World\"
"
        ),
        (
            "-",
            1,
            sub_exprs,
            true,
            "Subtracts all items from the first. Only works with Nums.
Example: (- 2 1 1) ; 0
"
        ),
        (
            "*",
            1,
            mult_exprs,
            true,
            "Multiply all items against the first. Works with Nums and (String Num*)
Example: (* 1 2 3) ; 6
         (* \"abc\" 3) ; \"abcabcabc\"
"
        ),
        (
            "%",
            2,
            rem_exprs,
            true,
            "Take the remainder of the first item against the second.
            Example: (% 4 2) ; 0"
        ),
        (
            "/",
            2,
            div_exprs,
            true,
            "Divide the first element by the rest.
Example: (/ 8 2 2 2) ; 1
"
        ),
        (
            "sqrt",
            1,
            sqrt_exprs,
            true,
            "Take the square root of a number. There's minor precision loss as it's way faster to convert to floats internally over using a bigdecimal.
Example: (sqrt 9) ; 3
"
        ),
        (
            "=",
            1,
            eq_exprs,
            true,
            "Test if all items are equal.
Example: (= 1 1) ; true
         (= 1) ; true
"
        ),
        (
            "<",
            2,
            lt_exprs,
            true,
            "Test if the first item is strictly smaller than the rest.
            Example: (< 0 1 2) ; true"
        ),
        (
            "<=",
            2,
            lte_exprs,
            true,
            "Test if the first item is smaller or equal to the rest.
            Example: (<= 0 0 0.05 1) ; true"
        ),
        (
            ">",
            2,
            gt_exprs,
            true,
            "Test if the first item is strictly greater than the rest.
            Example: (> 10 0 1 2 3 4) ; true"
        ),
        (
            ">=",
            2,
            gte_exprs,
            true,
            "Test if the first item is greater than or equal to the rest.
            Example: (>= 10 10 5) ; true"
        ),
        ("inc", 1, inc_exprs, true, "Increment the given number.
Example:
(inc 2.2) ;; 3.3
(inc 1) ;; 2
"),
        ("dec", 1, dec_exprs, true, "Decrement the given number.
Example:
(dec 2.2) ;; 3.3
(dec 1) ;; 2
"),
        ("pow", 2, pow, true, "Raise a number to an exponent.
Example:
(pow 2 3) ;; 8
(pow 10 3) ;; 1000
"),
        ("floor", 1, floor, true, "Floor a number.
Example:
(floor 5.5) ;; 5.5
"),
        ("int", 1, int, true, "Create an integer from the input.

Example:
(int 3.2) ;; 3
"),
        (
            "not",
            1,
            not,
            true,
            "Invert the bool. true becomes false and vice-versa."
        ),
        ("or", 1, or, true, "logical or."),
        ("and", 1, and, true, "logical and."),
        ("xor", 1, xor, true, "logical xor."),
        // // MISC
        (
            "ident",
            0,
            ident,
            true,
            "Identity function. Returns what you give it."
        ),
        (
            "quote",
            0,
            quote,
            false,
            "Transforms the given input into a quote. Usually you will want to use the '(1 2 3) syntax."
        ),
        (
            "symbol",
            0,
            symbol,
            false,
            "Turn a string into a symbol"
        ),
        (
            "str",
            1,
            string,
            true,
            "Make a string"
        ),
        (
            "print",
            1,
            print,
            true,
            "Print the given argument WITHOUT a newline."
        ),
        (
            "println",
            1,
            println,
            true,
            "Print the given argument WITH a newline."
        ),
        (
            "split",
            2,
            split,
            true,
            "Split a string with some substring.
Example:
>>> (split \",\" \"hello, world\")
(tuple \"hello\" \" world\")
"
        ),
        (
            "replace",
            3,
            replace,
            true,
            "Replace a substring in a string with some other string.
Example:
>>> (replace \"abc\" \"OwO\" \"abc def\")
\"OwO def\""
        ),
        (
            "ident-exists",
            1,
            ident_exists,
            false,
            "Returns true if a given symbol exists in the interpeter"
        ),
        (
            "eval",
            1,
            eval,
            true,
            "Eval an expression.
Example (in repl):
>>> '(+ 1 2)
(+ 1 2)
>>> (eval '(+ 1 2))
3"
        ),
        (
            "def",
            2,
            def,
            false,
            "Associate a given symbol with a value. Overwrites local variables.
Example:
>>> (def a 3)
>>> a
3
"
        ),
        ("cond", 2, cond, false, "Branching control flow construct. Given an even list of [pred then], if `pred` is true, return `then`.
Example:
(def input 10)
(cond
  (= input 3)  (print \"input is 3\")
  (= input 10) (print \"input is 10\")
  true         (print \"hit base case, input is: \" input))
"),
        ("match", 3, expr_match, false, "Branching control flow construct. Given an item and an even list of [value then], if `item` == `value`, return `then`.
Example:
(def input 10)
(match input
  3  (print \"input is 3\")
  10 (print \"input is 10\")
  _  (print \"hit base case, input is: \" input))
"),

        ("if", 3, if_gate, false, "Branching control flow construct. Given pred?, then, and else, if pred? is true, return then, otherwise, else.
Note: Does not evaluate branches not taken.
Example:
(def input 10)
(if (= input 10)
  (print \"input is 10!\")
  (print \":[ input is not 10\"))
"),
        ("shuffle", 1, shuffle, true, "Shuffle (randomize) a given list.
Example:
>>> (shuffle (range 10))
(6 3 2 9 4 0 1 8 5 7)
"),
        ("random_bool", 0, random_bool, true, "Randomly return true or false."),
        ("random_int", 2, random_int, true, "Randomly return an integer between lower and upper.

Example:
(random_int 0 10) ;; Returns a num between 0 and 10 (exclusive)"),
        ("panic", 1, panic, true, "Abort the program printing the given message.

Example: (panic \"goodbye\") ; kills program

Your console will print the following:

thread 'main' panicked at 'goodbye', src/stdlib.rs:216:5
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace

... and the interpreter will stop.
"),
        ("primes", 1, primes, true, "Prime numbers less than `n`."),
        ("divisors", 1, divisors, true, "Divisors of `n`."),
        ("sleep", 1, sleep, true, "Sleep for n seconds.
            Example: (sleep 10) ; sleep for 10 seconds."),
        ("type", 1, type_of, true, "Return the type of the argument as a string.
            Example: (type \"hello\") ; str"),
        ("doc", 1, doc, false, "Return the documentation of a symbol as a string.
            Example: (doc doc) ; Return the documentation of a symbol as a..."),
        ("err", 1, err, true, "Return an error with a message string.
            Example: (err \"Something bad happened!\") ; return an error"),
        ("all-symbols", 0, all_symbols, true, "Return all symbols defined in the interpreter."),
        ("include", 1, include, true, "Include a file into the interpreter."),
        // FUNC TOOLS
        ("map", 1, map, true, "Apply a function to each element of a sequence and return a list.
Example: (map inc '(1 2 3)) ; (2 3 4)
"),
        ("inline_transform", 2, inline_transform, true, "Given a list of data and another of functions, apply each function pairwise onto the list.
Example:

(defn adder-maker (x) (fn (y) (+ x y)))

(inline_transform
  '(1 1 1)
   (list (adder-maker 1) (adder-maker 2) (adder-maker 3)))  ;; ^(2 3 4)
"),
        ("foreach", 2, foreach, true, "Eagerly apply the given function to a sequence or list.
Example:
(foreach
  (fn (x) (println x))
  (range 20)) ; prints 0 to 20. Returns ().

(foreach
  (fn (x) (println x))
  (take 5 (map (fn (x) (* x x x x x x)) (range)))) ; prints 0, 1, 64, 729, 4096
"),
        ("filter", 1, filter, true, "Retain elements in a sequence according to a predicate.
Example:
(defn is-odd (x) (= 1 (% x 2)))
(filter is-odd (range 20)) ; outputs (1 3 5 7 9 11 13 15 17 19)
"),
        ("any", 2, any, true, "Ask whether a predicate is true in some sequence. Short circuits."),
        ("all", 2, all, true, "Ask whether a predicate is true for every element of a sequence. Short circuits."),
        ("lazy", 1, lazy, true, "Turn a list into a lazy sequence. Useful for building complex iterators over some source list."),
        ("skip", 2, skip, true, "Skip some amount in a lazy iterator."),
        ("product", 1, CartesianProduct::lisp_res, true, "Cartesian Product every list passed in.
Example:
>>> (doall (product '(0 1) '(0 1) '(0 1)))
(
  (tuple 0 0 0)
  (tuple 1 0 0)
  (tuple 0 1 0)
  (tuple 1 1 0)
  (tuple 0 0 1)
  (tuple 1 0 1)
  (tuple 0 1 1)
  (tuple 1 1 1)
)
"),
        ("apply", 2, apply, true, "Apply a function to a given list.
(def my-list '(1 2 3))
(apply + my-list) ; outputs 6
"),
        ("do", 1, exprs_do, false, "Evaluate a sequence of expressions and return the last one.
Example:
(defn complex-fn (x)
  (do
    (print \"current state: \" x)
    (+ x x)))
"),
        ("comp", 1, comp, true, "Compose given functions and return a new function. NOT IMPLEMENTED YET!"),
        ("reduce", 2, reduce, true, "Reduce (fold) a given sequence using the given function. Reduce is multi-arity, and will accept an `init` parameter.
Example:
(reduce + '(1 2 3)) ; 6
(reduce + 100 '(1 2 3)) ; 106
"),
        // Functions
        ("fn", 0, func, false, "Create a anonymous function.
Example:
(fn (x) (* x 2)) ; Fn<AnonFn, 1, [ x ]>
"),
        ("defn", 3, defn, false, "Define a function and add it to the symbol table. Supports doc strings.
Example:
(defn is-odd? (x) (= 1 (% x 2)))
(defn get-odd-numbers
  \"Extract the odd numbers out of the given sequence `x`\"
  (x)
  (filter is-odd? x)) ; for fun, try (doc get-odd-numbers)
"),
        ("anon-fn-sugar", 1, anon_fn_sugar, false,
         "Create an anonymous, automatic binding function. You normally want to use the #(+ 1 2) syntax. Fields are labelled $1, $2, $3, and so on.

Example:

(#(+ $1 $2) 1 2) ;; 3
(anon-fn-sugar (+ $1 $2)) ;; Fn<AnonFn, 0, [ ]>


Note: This currently does not capture values.

;; >>> (def foo (fn (x) #(+ $1 x)))
;; nil
;; >>> ((foo 3) 5)
;; Error: Unknown Symbol x
;;
;; Stacktrace:
;;   - Error in Fn<AnonFn, 0, [ ]>, with args (5)
"),
        ("bind", 2, bind, false, "Bind symbol-value pairs, adding them to the symbol table.
Example:
(defn quicksort
  \"Sort a list.\"
  (l)
  (cond
   (empty? l) l
   true (bind
         (pivot (head l)
          rest  (tail l)
          le    (filter (fn (x) (<= x pivot)) rest)
          ge    (filter (fn (x) (> x pivot)) rest))
         (+ (quicksort le) (list pivot) (quicksort ge)))))
"),
        // Iterators
        ("take", 2, take, true, "Take the first `n` items from a list or sequence.
Example:
(take 2 '(1 2 3)) ; (1 2)
(take 5 (range)) ; lazy seq of (0 1 2 3 4)
(doall (take 5 (range))) ; (0 1 2 3 4)
"),
        ("find", 2, find, true, "Find and return some value matching a predicate in an iterator.

Note: This will stop iterating once it's found an item. If nothing is found, nil is returned.

Example:

>>> (find #(= $1 3) (take 4 (range)))
3
>>> (find #(= $1 300) (take 4 (range)))
nil
"),
        ("slice", 3, slice, true, "Slice a list.
Example:

>>> (def ll '(1 2 3 4 5 6))
nil
>>> (slice 0 2 ll)
(tuple 1 2)
"),
        ("take-while", 2, take_while, true, "Continue taking items while `pred` is true.
Example:
(defn less-than-five (x) (< x 5))
(doall (take-while less-than-five (range))) ; (0 1 2 3 4)
(take 2 '(1 2 3)) ; (1 2)
(take 5 (range)) ; lazy seq of (0 1 2 3 4)
(doall (take 5 (range))) ; (0 1 2 3 4)
"),
        ("doall", 1, doall, true, "Evaluate a sequence, collecting the results into a list.
Example:
(doall (take 5 (range))) ; (0 1 2 3 4)
"),
        // Dicts
        ("dict", 0, make_dict, true, "Create a dict from the given elements.
Example:
(dict \"a\" 1 \"b\" 2) ;
"),
        ("assoc", 1, assoc, true, "Create a new dict from an old dict with the given elements.
Example:
(assoc (dict) 1 2 3 4) ; {1: 2, 3: 4}
"),
        ("remove", 2, remove, true, "Remove a key-value pair from a dict.
Example:
(remove (dict 1 2) 1) ; {}
"),
        ("set", 3, set_dict, true, "Set a key to a value in a dict. It'll return the new dict.
Example:
(set (dict 1 2) 3 4) ; {1: 2, 3: 4}
(get (dict) 1 2) ; {1: 2}
"),
        ("values", 1, values, true, "Get the values of a dict.
Example:
>>> (values (dict 1 2 3 4))
(tuple 2 4)"),
        ("get", 2, get_dict, true, "Get a value from a dict by key.
Example:
(get (dict 1 2) 1) ; 2
(get (dict) 1) ; nil
"),
        // Lists
        ("list", 0, list, true, "Create a list from the given elements.
Example:
(list 1 2 3) ; (1 2 3)
"),
        ("tuple", 0, tuple, true, "Create a list from the given elements.
(tuple 1 2 3) ; (tuple 1 2 3)
;; It's usually easier to use the tuple syntax:
^(1 2 3) ; (tuple 1 2 3)
"),
        ("nth", 2, nth, true, "Extract the nth item from a list or tuple. Throws error if this fails.
Example
(nth 0 ^(1 2 3)) ; 1
(nth 1 '(1 2 3)) ; 2
"),
        ("flatten", 1, flatten, true, "Flatten a list of lists.
Example:
>>> (flatten '('(1 2 3) '(4 5 6) 7))
(tuple 1 2 3 4 5 6 7)
"),
        ("chars", 1, chars, true, "Get a tuple of characters from a string.
Example:
(chars \"hello\") ;; (tuple \"h\" \"e\" \"l\" \"l\" \"o\")
"),
        ("head", 1, head, true, "Get the first item in a list.
Example:
(head ()) ; nil
(head (1 2 3)) ; 1
"),
        ("tail", 1, tail, true, "Get all items after the first in a list or tuple.
(tail '(1 2 3)) ; (2 3)
(tail ^()) ; nil
"),
        ("cons", 2, cons, true, "Push an item to the front of a list.
Example:
(cons 1 '()) ; (1)
(cons 1 '(2 3)) ; (1 2 3)
"),
        ("range", 0, range, true, "Generate a range of numbers. It accepts 0, 1, or 2 arguments. No arguments
yields an infinite range, one arg stops the range at that arg, and two args denote start..end.
Example:
(range) ; infinite range
(range 5) ; (0 1 2 3 4)
(range 5 10); (5 6 7 8 9)
"),
        // ("product", 2, product, true, "Cartesian product two lists"),
        ("len", 1, len, true, "Get the number of items in a list or tuple.
Example:
(len '(0 0 0)) ; 3
(len '()) ; 0
"),
        ("rev", 1, rev, true, "Reverse a list."),
        ("zip", 2, zip, true, "Zip two lists together into a list of tuples."),
        ("len", 1, len, true, "Get the number of items in a list or tuple.
Example:
(len '(0 0 0)) ; 3
(len '()) ; 0
"),

        ("sort", 1, sort, true, "Sort a given homogeneously typed list in ascending order. Returns an error if types are all not the same.
Example:
(sort '(3 7 0 5 4 8 1 2 6 9)) ; (0 1 2 3 4 5 6 7 8 9)
"),
        ("distinct", 1, distinct, true, "Remove all duplicates from a list. This will sort the list.
Example:
(distinct '(1 1 1 2 2 0 0)) ; (0 1 2)
"),

        ("max-by", 2, max_by, true, "Get the maximum value of an iterator by a some function f. Throws an error if called with an empty iteratable.
Example:
(max-by
  (fn (x) (nth 0 x))
  (lazy (zip (range 10) (range 10)))) ;; (tuple 9 9)"),
        ("fs::open", 1, FileRecord::from_x7, true, "Open a file. Under construction."),
        ("re::compile", 1, RegexRecord::compile_x7, true, "Compile a regex. Under construction."),
        ("defrecord", 1, DynRecord::defrecord, false, "Define a Record structure.

Use defmethod to add methods a record.

Example:
;; Define a record
(defrecord Vec3 \"Three Dimensional Vector\" x y z)

;; Instantiate a Vec3
(def v (Vec 1 2 3))

;; Access attributes

v.x    ;; 1
(.y v) ;; 2
"),
        ("defmethod", 1, DynRecord::defmethod_x7, false, "Add a method to a record. Cannot be called on instantiated records.

NOTE: Methods get an implicit `self` reference.

;; Example

;; Define a record
(defrecord Vec3 \"Three Dimensional Vector\" x y z)

(defmethod Vec3 +
  \"Add two vectors together\"
  (other)
  (Vec3
   (+ other.x self.x)
   (+ other.y self.y)
   (+ other.z self.z)))

(def v (Vec3 1 1 1))

(.+ v v) ;; (Vec3 2 2 2)"),
        ("call_method", 2, call_method, true, "
Call a method on a record.

Example:

(def f (fs::open \"Hello.txt\"))
(call_method f \"read_to_string\") ;; no args required
(call_method f \"write\" \"hello world\") ;; pass it an arg
"),
        ("methods", 1, doc_methods, true, "Grab all documentation for a record's methods"),
        ("time", 1, time, false, "Return the time taken to evaluate an expression in milliseconds.")
    );
    if !opts.do_not_load_native_stdlib {
        if let Err(e) = load_x7_stdlib(opts, &syms) {
            panic!("Failed to load stdlib: {:?}", e);
        }
    }
    document_records!(syms, FileRecord);
    document_records!(syms, RegexRecord);
    syms
}
