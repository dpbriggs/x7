use itertools::Itertools;
use num_traits::cast::ToPrimitive;
use std::collections::HashMap;
use std::sync::Arc;
use std::{error::Error, path::Path};

use crate::interner::InternedString;
use crate::symbols::{Expr, Function, SymbolTable};
use crate::{parser::read, symbols::LispResult};
use anyhow::anyhow;
use im::Vector;

/// ForeignData is a trait that allows x7 to reason about
/// foreign data types by mapping Self to x7's Expr
/// and vice-versa.
///
/// As the mapping may not be 1:1, all conversions are fallible
/// result types.
pub trait ForeignData
where
    Self: Sized,
{
    /// Convert from Self to x7's Expr type.
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>>;
    /// Convert x7's Expr type to Self.
    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>>;
}

/// Struct to help type erase anyhow::Error to ease
/// interfacing with external programs.
struct ErrorBridge(anyhow::Error);

impl std::error::Error for ErrorBridge {}

impl ErrorBridge {
    #[allow(clippy::new_ret_no_self)]
    fn new(err: anyhow::Error) -> Box<dyn Error + Send> {
        Box::new(ErrorBridge(err))
    }
}

impl std::fmt::Debug for ErrorBridge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for ErrorBridge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// A x7 interpreter instance.
///
/// This type can be safely and cheaply cloned. This will copy
/// modifications to the symbol table (def, defn, foreign functions, etc).
///
/// # Example
///
/// ```rust
/// use x7::ffi::X7Interpreter;
///
/// let interpreter = X7Interpreter::new();
/// ```
///
/// Thread Safety Note:
///
/// Running several instances of the same interpreter (cloned)
/// in parallel means that modifications to the symbol table
/// may not be reflected at the same time in all threads.
///
/// e.g. Running the following programs in parallel:
///
/// - (def data-race "owo")
/// - (println data-race)
///
/// Will result in either 'Undefined Symbol: data-race'
/// or printing "owo" to console.
///
/// Async Note: x7 has blocking IO, so you shouldn't run it in async contexts.
#[derive(Clone)]
pub struct X7Interpreter {
    symbol_table: SymbolTable,
}

impl Default for X7Interpreter {
    fn default() -> Self {
        X7Interpreter::new()
    }
}

impl X7Interpreter {
    /// Make a new interpreter instance.
    pub fn new() -> Self {
        X7Interpreter {
            symbol_table: crate::stdlib::create_stdlib_symbol_table_no_cli(),
        }
    }

    /// Recursively load a provided standard library directory.
    pub fn load_lib_dir<P: AsRef<Path>>(&self, lib_path: P) -> Result<(), Box<dyn Error>> {
        crate::modules::recursively_load_dir(false, lib_path, &self.symbol_table)
    }

    /// Add a foreign function to this x7 interpreter instance.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use x7::ffi::{ExprHelper, ForeignData, X7Interpreter};
    /// use std::sync::Arc;
    ///
    /// let interpreter = X7Interpreter::new();
    /// let my_sum_fn = |args: Vec<u64>| Ok(args.iter().sum());
    /// // Add the my-sum to interpreter
    /// interpreter.add_function_ptr("my-sum", 1, Arc::new(my_sum_fn));
    ///
    /// // And verify we get u64 with value 6 out of it.
    /// assert_eq!(interpreter.run_program::<u64>("(my-sum 1 2 3)").unwrap(), 6);
    /// ```
    ///
    /// For further help, please find the ffi example at:
    /// <https://github.com/dpbriggs/x7/blob/master/examples/ffi.rs>
    #[allow(clippy::type_complexity)]
    pub fn add_function_ptr<T: 'static + ForeignData>(
        &self,
        function_symbol: &str,
        minimum_args: usize,
        f: Arc<dyn Fn(Vec<T>) -> Result<T, Box<dyn Error + Send>> + Sync + Send>,
    ) {
        let x7_fn = move |args: Vector<Expr>, _sym: &SymbolTable| {
            let args: Result<Vec<_>, _> = args.iter().map(|item| T::from_x7(item)).collect();
            args.and_then(|args| (f)(args).and_then(|e| e.to_x7()))
                .map_err(|e| anyhow!("{:?}", e))
        };
        let x7_fn = Arc::new(x7_fn);

        let f = Function::new(function_symbol.into(), minimum_args, x7_fn, true);
        self.symbol_table
            .add_symbol(function_symbol.into(), Expr::function(f))
    }

    /// Add a foreign function to this x7 interpreter instance.
    ///
    /// You'll want to use `.to_x7_fn()` here.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use x7::ffi::{ExprHelper, ForeignData, X7Interpreter, IntoX7Function};
    ///
    /// let interpreter = X7Interpreter::new();
    /// let my_sum_fn = |a: u64, b: u64| a + b;
    ///
    /// // Add the function
    /// interpreter.add_function("my-sum", my_sum_fn.to_x7_fn());
    ///
    /// // Verify the output is correct
    /// assert_eq!(interpreter.run_program::<u64>("(my-sum 1 2)").unwrap(), 3);
    /// ```
    ///
    /// For further help, please find the ffi example at:
    /// <https://github.com/dpbriggs/x7/blob/master/examples/ffi.rs>
    pub fn add_function(
        &self,
        function_symbol: &'static str,
        fn_tuple: (usize, crate::symbols::X7FunctionPtr),
    ) {
        let (minimum_args, fn_ptr) = fn_tuple;
        let f = Function::new(function_symbol.into(), minimum_args, fn_ptr, true);
        self.symbol_table
            .add_symbol(function_symbol.into(), Expr::function(f));
    }

    /// Add a foreign function to this x7 interpreter instance, that doesn't
    /// evaluate it's arguments.
    ///
    /// Useful when dynamically generating functions.
    ///
    /// You'll want to use `.to_x7_fn()` here.
    pub fn add_unevaled_function(
        &self,
        function_symbol: &'static str,
        fn_tuple: (usize, crate::symbols::X7FunctionPtr),
    ) {
        let (minimum_args, fn_ptr) = fn_tuple;
        let f = Function::new(function_symbol.into(), minimum_args, fn_ptr, false);
        self.symbol_table
            .add_symbol(function_symbol.into(), Expr::function(f));
    }

    /// Manually construct an x7 function, and add it to the interpreter.
    ///
    /// #Example
    ///
    /// ```rust
    /// use x7::ffi::{IntoX7Function, Variadic, X7Interpreter};
    /// use x7::symbols::Expr;
    ///
    /// fn embed_foreign_script(interpreter: &X7Interpreter) {
    ///     // (def-dyn-function my-sum (a b) (+ a b))
    ///     let interpreter_clone = interpreter.clone();
    ///     let f = move |args: Variadic<Expr>| {
    ///         let args = args.into_vec();
    ///         let fn_name = match args[0].get_symbol_string() {
    ///             Ok(sym) => sym,
    ///             Err(e) => return Err(e),
    ///         };
    ///         let f_args = args[1].clone(); // (arg1 arg2)
    ///         let f_body = args[2].clone(); // (redis "set" arg1 arg2)
    ///         let res = interpreter_clone.add_dynamic_function(fn_name, f_args, f_body);
    ///         res
    ///     };
    ///     interpreter
    ///         .add_unevaled_function("def-dyn-function", f.to_x7_fn());
    /// }
    /// ```
    pub fn add_dynamic_function<I: Into<InternedString>>(
        &self,
        function_sym: I,
        named_args: Expr,
        body: Expr,
    ) -> LispResult<Expr> {
        let arg_symbols = named_args.get_list()?;
        let args_len = arg_symbols.len();
        let interned_fn_name = function_sym.into();
        let f = Arc::new(move |_args: Vector<Expr>, sym: &SymbolTable| body.eval(sym));
        let f = Function::new_named_args(
            interned_fn_name,
            args_len,
            f,
            arg_symbols
                .into_iter()
                .map(|e| e.get_symbol_string())
                .try_collect()?,
            true,
            HashMap::new(),
        )?;

        self.symbol_table
            .add_symbol(interned_fn_name, Expr::function(f));
        Ok(Expr::Nil)
    }

    /// Run an x7 program.
    ///
    /// # Example:
    ///
    /// ```rust
    /// use x7::ffi::{ExprHelper, ForeignData, X7Interpreter, IntoX7Function};
    ///
    /// let interpreter = X7Interpreter::new();
    /// let my_sum_fn = |args: Vec<u64>| args.iter().sum::<u64>();
    /// // Add the my-sum to interpreter
    /// interpreter.add_function("my-sum", my_sum_fn.to_x7_fn());
    ///
    /// // And verify we get u64 with value 6 out of it.
    /// assert_eq!(interpreter.run_program::<u64>("(my-sum '(1 2 3))").unwrap(), 6);
    /// ```
    ///
    /// For further help, please find the ffi example at:
    /// <https://github.com/dpbriggs/x7/blob/master/examples/ffi.rs>
    pub fn run_program<T: 'static + ForeignData>(
        &self,
        program: &str,
    ) -> Result<T, Box<dyn Error + Send>> {
        let mut last_expr = Expr::Nil;
        for expr in read(program) {
            last_expr = expr
                .and_then(|expr| expr.eval(&self.symbol_table))
                .map_err(ErrorBridge::new)?;
        }
        T::from_x7(&last_expr)
    }

    /// Run a function directly in the interpreter.
    ///
    /// This is useful for dynamic functions, where you
    /// just want to call the foreign function.
    ///
    /// # Example
    ///
    /// ```rust
    /// use x7::ffi::{ExprHelper, ForeignData, X7Interpreter, IntoX7Function};
    ///
    /// let interpreter = X7Interpreter::new();
    /// // replace "+" with your foreign function
    /// let res: u64 = interpreter.run_function("+", &[1u64, 2, 3]).unwrap();
    /// assert_eq!(res, 6);
    /// ```
    pub fn run_function<T: ForeignData, Out: ForeignData>(
        &self,
        fn_name: &str,
        fn_args: &[T],
    ) -> Result<Out, Box<dyn Error + Send>> {
        let args = fn_args
            .iter()
            .map(|e| e.to_x7())
            .collect::<Result<_, _>>()?;
        self.symbol_table
            .lookup(&fn_name.into())
            .and_then(|f| f.call_fn(args, &self.symbol_table))
            .map_err(ErrorBridge::new)
            .and_then(|e| Out::from_x7(&e))
    }
}

/// Trait to help convert x7's Expr to primitive types.
///
/// Conversions are always fallible as you can call
/// it on a wrong variant, or the primitive conversion
/// may not be possible (e.g. Expr::Num(2^100).to_u64())
pub trait ExprHelper {
    fn to_u64(&self) -> Result<u64, Box<dyn Error + Send>>;
    fn to_i64(&self) -> Result<i64, Box<dyn Error + Send>>;
    fn to_usize(&self) -> Result<usize, Box<dyn Error + Send>>;
    fn to_f64(&self) -> Result<f64, Box<dyn Error + Send>>;
    fn to_f32(&self) -> Result<f32, Box<dyn Error + Send>>;

    fn to_string(&self) -> Result<String, Box<dyn Error + Send>>;
}

impl ExprHelper for Expr {
    fn to_u64(&self) -> Result<u64, Box<dyn Error + Send>> {
        self.get_num().map_err(ErrorBridge::new).and_then(|n| {
            ToPrimitive::to_u64(&n)
                .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
        })
    }

    fn to_i64(&self) -> Result<i64, Box<dyn Error + Send>> {
        self.get_num().map_err(ErrorBridge::new).and_then(|n| {
            ToPrimitive::to_i64(&n)
                .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
        })
    }

    fn to_usize(&self) -> Result<usize, Box<dyn Error + Send>> {
        self.get_num().map_err(ErrorBridge::new).and_then(|n| {
            ToPrimitive::to_usize(&n)
                .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
        })
    }

    fn to_f64(&self) -> Result<f64, Box<dyn Error + Send>> {
        self.get_num().map_err(ErrorBridge::new).and_then(|n| {
            ToPrimitive::to_f64(&n)
                .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
        })
    }

    fn to_f32(&self) -> Result<f32, Box<dyn Error + Send>> {
        self.get_num().map_err(ErrorBridge::new).and_then(|n| {
            ToPrimitive::to_f32(&n)
                .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
        })
    }

    fn to_string(&self) -> Result<String, Box<dyn Error + Send>> {
        self.get_string().map_err(ErrorBridge::new)
    }
}

impl ExprHelper for bigdecimal::BigDecimal {
    fn to_u64(&self) -> Result<u64, Box<dyn Error + Send>> {
        ToPrimitive::to_u64(self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
    }

    fn to_i64(&self) -> Result<i64, Box<dyn Error + Send>> {
        ToPrimitive::to_i64(self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
    }

    fn to_usize(&self) -> Result<usize, Box<dyn Error + Send>> {
        ToPrimitive::to_usize(self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
    }

    fn to_f64(&self) -> Result<f64, Box<dyn Error + Send>> {
        ToPrimitive::to_f64(self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
    }

    fn to_f32(&self) -> Result<f32, Box<dyn Error + Send>> {
        ToPrimitive::to_f32(self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))
    }

    fn to_string(&self) -> Result<String, Box<dyn Error + Send>> {
        Ok(ToString::to_string(&self))
    }
}

// This is hubris, but let's do it so the README looks nice.

impl ForeignData for u64 {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        Ok(Expr::Num((*self).into()))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_u64()
    }
}

impl ForeignData for u32 {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        Ok(Expr::Num((*self).into()))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_u64().map(|e| e as u32)
    }
}

impl ForeignData for i64 {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        Ok(Expr::Num((*self).into()))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_i64()
    }
}

impl ForeignData for usize {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        let n = num_traits::FromPrimitive::from_usize(*self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))?;
        Ok(Expr::Num(n))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_usize()
    }
}

impl ForeignData for f32 {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        // use num_traits::FromPrimitive;
        let n = num_traits::FromPrimitive::from_f32(*self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))?;
        Ok(Expr::Num(n))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_f32()
    }
}

impl ForeignData for f64 {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        // use num_traits::FromPrimitive;
        let n = num_traits::FromPrimitive::from_f64(*self)
            .ok_or_else(|| ErrorBridge::new(anyhow!("Could not convert {} to u64", self)))?;
        Ok(Expr::Num(n))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        expr.to_f64()
    }
}

impl ForeignData for String {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        Ok(Expr::string(self.clone()))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        Ok(format!("{}", expr))
    }
}

impl<T: ForeignData> ForeignData for Vec<T> {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        Ok(Expr::Tuple(
            self.iter()
                .map(T::to_x7)
                .collect::<Result<Vector<_>, _>>()?,
        ))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        let res = expr
            .get_list()
            .map_err(ErrorBridge::new)?
            .iter()
            .map(T::from_x7)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(res)
    }
}

impl<T: ForeignData> ForeignData for Result<T, Box<dyn Error + Send>> {
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>> {
        match self {
            Ok(t) => t.to_x7(),
            Err(e) => Err(ErrorBridge::new(anyhow!("{:?}", e))),
        }
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        Ok(T::from_x7(expr))
    }
}

pub struct Variadic<T>(Vec<T>);

impl<T> Variadic<T> {
    /// Consume the Variadic to produce Vec<T>
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

// We can use some trait magic to make functions easier to do

pub trait IntoX7Function<Args, Out> {
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr);
}

macro_rules! convert_arg {
    ($t:ident, $e:expr) => {{
        match $t::from_x7($e) {
            Ok(v) => v,
            Err(e) => return Err(anyhow!("{:?}", e)),
        }
    }};
}

impl<F, A, Out> IntoX7Function<(A,), Out> for F
where
    A: ForeignData,
    Out: ForeignData,
    F: Fn(A) -> Out + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            #[allow(clippy::redundant_closure)]
            let res = A::from_x7(&args[0]).map(|e| (self)(e));
            res.and_then(|e| e.to_x7()).map_err(|e| anyhow!("{:?}", e))
        };
        (1, Arc::new(f))
    }
}

impl<F, T: ForeignData, Out> IntoX7Function<(Variadic<T>,), Out> for F
where
    T: ForeignData,
    Out: ForeignData,
    F: Fn(Variadic<T>) -> Out + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            let args = match args.iter().map(T::from_x7).collect::<Result<Vec<_>, _>>() {
                Ok(v) => v,
                Err(e) => return Err(anyhow!("{:?}", e)),
            };
            (self)(Variadic(args))
                .to_x7()
                .map_err(|e| anyhow!("{:?}", e))
        };
        (1, Arc::new(f))
    }
}

// We're working with a function with two arguments,
// that returns a single output type Out.
impl<F, A, B, Out> IntoX7Function<(A, B), Out> for F
where
    // All inputs and outputs to this function require ForeignData
    A: ForeignData,
    B: ForeignData,
    Out: ForeignData,
    // X7FunctionPtr requires Sync + Send, so we add that restriction to F
    F: Fn(A, B) -> Out + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        // this closure conforms to the shape X7FunctionPtr requires,
        // namely a function that takes a Vector<Expr> and a symbol table reference.
        // args: (+ 1 2) -> vector![Expr::Num(1), Expr::Num(2)]
        // _sym: A symbol table reference. Unused.
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            // exact_len: macro to throw an error if args.len() != 2.
            crate::exact_len!(args, 2);
            // convert_arg: Calls A::to_x7(&args[0]) and makes a nice error
            let a = convert_arg!(A, &args[0]);
            let b = convert_arg!(B, &args[1]);
            (self)(a, b) // (self)(a,b) calls the foreign function with args a, b
                .to_x7() // map the output with Out::to_x7
                .map_err(|e| anyhow!("{:?}", e)) // massage error type to x7's error type (anyhow)
        };
        // Finally, return a tuple of minimum args + our function
        (2, Arc::new(f))
    }
}

impl<F, A, B, C, Out> IntoX7Function<(A, B, C), Out> for F
where
    A: ForeignData,
    B: ForeignData,
    C: ForeignData,
    Out: ForeignData,
    F: Fn(A, B, C) -> Out + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 3);
            let a = convert_arg!(A, &args[0]);
            let b = convert_arg!(B, &args[1]);
            let c = convert_arg!(C, &args[2]);
            (self)(a, b, c).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        (3, Arc::new(f))
    }
}

impl<F, A, B, C, D, Out> IntoX7Function<(A, B, C, D), Out> for F
where
    A: ForeignData,
    B: ForeignData,
    C: ForeignData,
    D: ForeignData,
    Out: ForeignData,
    F: Fn(A, B, C, D) -> Out + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 4);
            let a = convert_arg!(A, &args[0]);
            let b = convert_arg!(B, &args[1]);
            let c = convert_arg!(C, &args[2]);
            let d = convert_arg!(D, &args[3]);
            (self)(a, b, c, d).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        (4, Arc::new(f))
    }
}

impl<F, A, B, C, D, E, Out> IntoX7Function<(A, B, C, D, E), Out> for F
where
    A: ForeignData,
    B: ForeignData,
    C: ForeignData,
    D: ForeignData,
    E: ForeignData,
    Out: ForeignData,
    F: Fn(A, B, C, D, E) -> Out + Sync + Send + 'static,
{
    #[allow(clippy::many_single_char_names)]
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 5);
            let a = convert_arg!(A, &args[0]);
            let b = convert_arg!(B, &args[1]);
            let c = convert_arg!(C, &args[2]);
            let d = convert_arg!(D, &args[3]);
            let e = convert_arg!(E, &args[4]);
            (self)(a, b, c, d, e)
                .to_x7()
                .map_err(|e| anyhow!("{:?}", e))
        };
        (5, Arc::new(f))
    }
}

impl<F> IntoX7Function<(Variadic<Expr>,), Expr> for F
where
    F: Fn(Variadic<Expr>) -> LispResult<Expr> + Sync + Send + 'static,
{
    fn to_x7_fn(self) -> (usize, crate::symbols::X7FunctionPtr) {
        let f = move |args: Vector<Expr>, _sym: &SymbolTable| {
            let args = args.iter().cloned().collect();
            (self)(Variadic(args))
        };
        (1, Arc::new(f))
    }
}
