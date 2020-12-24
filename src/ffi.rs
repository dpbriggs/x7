use std::error::Error;
use std::sync::Arc;

use crate::parser::read;
use crate::symbols::{Expr, Function, SymbolTable};
use anyhow::anyhow;
use im::Vector;

pub trait ForeignData
where
    Self: Sized,
{
    fn to_x7(&self) -> Result<Expr, Box<dyn Error + Send>>;
    fn from_x7(expr: &Expr) -> Result<Self, Box<dyn Error + Send>>;
}

struct ErrorBridge(anyhow::Error);

impl std::error::Error for ErrorBridge {}

impl ErrorBridge {
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
pub struct X7Interpreter {
    symbol_table: SymbolTable,
}

impl Default for X7Interpreter {
    fn default() -> Self {
        X7Interpreter::new()
    }
}

impl X7Interpreter {
    pub fn new() -> Self {
        X7Interpreter {
            symbol_table: crate::stdlib::create_stdlib_symbol_table_no_cli(),
        }
    }

    pub fn add_function_test<T: 'static + ForeignData>(
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
