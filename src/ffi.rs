use num_traits::cast::ToPrimitive;
use std::error::Error;
use std::sync::Arc;

use crate::parser::read;
use crate::symbols::{Expr, Function, SymbolTable};
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
        write!(f, "{}", self.0)
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
    /// interpreter.add_function("my-sum", 1, Arc::new(my_sum_fn));
    ///
    /// // And verify we get u64 with value 6 out of it.
    /// assert_eq!(interpreter.run_program::<u64>("(my-sum 1 2 3)").unwrap(), 6);
    /// ```
    ///
    /// For further help, please find the ffi example at:
    /// https://github.com/dpbriggs/x7/blob/master/examples/ffi.rs
    pub fn add_function<T: 'static + ForeignData>(
        &self,
        function_symbol: &str,
        minimum_args: usize,
        f: Arc<dyn Fn(Vec<T>) -> Result<T, Box<dyn Error + Send>> + Sync + Send>,
    ) {
        let x7_fn = move |args: Vector<Expr>, _sym: &SymbolTable| {
            let args: Result<Vec<_>, _> = args.iter().map(|item| T::from_x7(item)).collect();
            args.and_then(|args| (f)(args).and_then(|e| e.to_x7()))
                .map_err(|e| anyhow!("{}", e))
        };
        let x7_fn = Arc::new(x7_fn);

        let f = Function::new(function_symbol.into(), minimum_args, x7_fn, true);
        self.symbol_table
            .add_symbol(function_symbol, Expr::Function(f))
    }

    /// Run an x7 program.
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
    /// interpreter.add_function("my-sum", 1, Arc::new(my_sum_fn));
    ///
    /// // And verify we get u64 with value 6 out of it.
    /// assert_eq!(interpreter.run_program::<u64>("(my-sum 1 2 3)").unwrap(), 6);
    /// ```
    ///
    /// For further help, please find the ffi example at:
    /// https://github.com/dpbriggs/x7/blob/master/examples/ffi.rs
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
        Ok(Expr::String(self.clone()))
    }

    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>> {
        Ok(format!("{}", expr))
    }
}
