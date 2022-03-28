use std::io::stdin;

use crate::{
    bad_types,
    symbols::{Expr, LispResult, Symbol, SymbolTable},
};
use anyhow::anyhow;
use im::Vector;

use super::ByteCodeCompiler;

#[derive(Debug, Clone)]
pub enum Instruction {
    Push(Expr),
    Test(usize),
    Jump(usize),
    Fail(&'static str),
    GlobalBind(Symbol),
    EnterScope,
    ExitScope,
    LocalScopeBind(Symbol),
    CallFn(usize),
    Ret,
    Pop,
    Halt,
}

pub struct ByteCodeVM {
    instp: usize,
    instp_stack: Vec<usize>,
    compiler: ByteCodeCompiler,
    program: Vec<Instruction>,
    stack: Vec<Expr>,
    root_symbol_table: SymbolTable,
    function_scopes: Vec<SymbolTable>,
    debug_mode: bool,
}

enum ControlFlow {
    Incr,
    Jump(usize),
}

impl ByteCodeVM {
    pub fn new(symbol_table: SymbolTable, debugger_flag: bool) -> Self {
        ByteCodeVM {
            instp: 0,
            instp_stack: Vec::new(),
            stack: Vec::new(),
            compiler: ByteCodeCompiler::new(),
            program: Vec::new(),
            root_symbol_table: symbol_table,
            function_scopes: vec![],
            debug_mode: debugger_flag,
        }
    }

    fn pop(&mut self) -> LispResult<Expr> {
        self.stack
            .pop()
            .ok_or_else(|| anyhow!("Pop called on empty stack!"))
    }

    fn push(&mut self, value: Expr) {
        self.stack.push(value)
    }

    pub fn pretty_print_program(&self) {
        println!(
            "--------------------------------------------------------------------------------"
        );
        for (idx, instruction) in self.program.iter().enumerate() {
            println!("{:<5}: {:?}", idx, instruction);
        }
        println!(
            "--------------------------------------------------------------------------------"
        );
    }

    pub fn run(&mut self, input: &str) -> LispResult<()> {
        let (program, named_funcs) = self.compiler.compile(input)?;
        self.program = program;
        for (func, doc) in named_funcs.into_iter() {
            let func_sym = func.symbol;
            self.root_symbol_table
                .add_symbol(func_sym, Expr::ByteCompiledFunction(func));
            if let Some(doc) = doc {
                self.root_symbol_table
                    .add_doc_item(func_sym.to_string(), doc);
            }
        }
        self.pretty_print_program();
        self.execute()
    }

    fn symbol_table(&self) -> &SymbolTable {
        match self.function_scopes.last() {
            Some(sym) => sym,
            None => &self.root_symbol_table,
        }
    }

    fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        match self.function_scopes.last_mut() {
            Some(sym) => sym,
            None => &mut self.root_symbol_table,
        }
    }

    fn add_function_scope(&mut self) {
        let new_sym = self.symbol_table().clone();
        self.function_scopes.push(new_sym)
    }

    fn remove_function_scope(&mut self) -> LispResult<()> {
        if let None = self.function_scopes.pop() {
            Err(anyhow!("No function scope to pop! {}", self.instp))
        } else {
            Ok(())
        }
    }

    fn record_instp(&mut self) {
        self.instp_stack.push(self.instp);
    }

    fn restore_instp(&mut self) -> LispResult<()> {
        self.instp = self
            .instp_stack
            .pop()
            .ok_or_else(|| anyhow!("No instp to restore!"))?;
        Ok(())
    }

    fn get_user_input(&mut self) {
        loop {
            let mut input = String::new();
            stdin().read_line(&mut input).unwrap();
            println!("{:<5}: {:?}", self.instp, self.program[self.instp]);
            match input.as_str().trim_end() {
                "n" => return,
                "pp" => self.pretty_print_program(),
                _ if input.starts_with("p ") => println!(
                    "{:?}",
                    self.symbol_table()
                        .lookup(&input.split_ascii_whitespace().nth(1).unwrap().into())
                ),
                _ => return,
            };
        }
    }

    fn execute(&mut self) -> LispResult<()> {
        while self.instp < self.program.len() {
            if self.debug_mode {
                self.get_user_input();
            }
            let res = match self.program[self.instp].clone() {
                Instruction::Push(expr) => {
                    // TODO: fast track primitive types
                    // TODO: Do we want to evaluate things we push?
                    self.stack.push(expr.eval(self.symbol_table())?);
                    ControlFlow::Incr
                }
                Instruction::Test(fail_loc) => {
                    let test = self.pop()?;
                    if test.is_truthy(self.symbol_table())? {
                        ControlFlow::Incr
                    } else {
                        ControlFlow::Jump(fail_loc)
                    }
                }
                Instruction::Jump(loc) => ControlFlow::Jump(loc),
                Instruction::LocalScopeBind(sym) => {
                    let value = self.pop()?;
                    self.symbol_table_mut().add_func_local_sym(sym, value)?;
                    // dbg!(&self.symbol_table().get_func_locals());
                    ControlFlow::Incr
                }
                Instruction::EnterScope => {
                    self.add_function_scope();
                    ControlFlow::Incr
                }
                Instruction::ExitScope => {
                    self.remove_function_scope()?;
                    ControlFlow::Incr
                }
                Instruction::Ret => {
                    self.restore_instp()?;
                    ControlFlow::Incr
                }
                Instruction::CallFn(num_args) => {
                    let function = self.pop()?;
                    // TODO: Handle records
                    match function {
                        Expr::Function(f) => {
                            // We're a built-in, so handle that
                            let mut args = Vector::new();
                            for _ in 0..num_args {
                                args.push_back(self.pop()?);
                            }
                            let res = f.call_fn(args, self.symbol_table())?;
                            self.push(res);
                            ControlFlow::Incr
                        }
                        Expr::ByteCompiledFunction(f) => {
                            if self.stack.len() < f.minimum_args {
                                return Err(anyhow!(
                                    "Expected {} args but could only supply {}",
                                    f.minimum_args,
                                    self.stack.len()
                                ));
                            }
                            self.record_instp();
                            ControlFlow::Jump(f.loc)
                        }
                        otherwise => return bad_types!("func", otherwise),
                    }
                }
                Instruction::Fail(reason) => {
                    return Err(anyhow!("{}", reason));
                }
                Instruction::Pop => {
                    self.pop()?;
                    ControlFlow::Incr
                }
                Instruction::GlobalBind(sym) => {
                    let value = self.pop()?;
                    self.symbol_table().add_symbol(sym, value);
                    ControlFlow::Incr
                }
                Instruction::Halt => break,
            };
            // dbg!(&self.stack);
            match res {
                ControlFlow::Incr => self.instp += 1,
                ControlFlow::Jump(loc) => self.instp = loc,
            }
        }
        Ok(())
    }
}
// (+ 1 2)
// push_arg 1
// push_arg 2
// CallFn +

// (defn foobar (x y) (* x y))
// push_deref x
// push_deref y
// CallFn *

// (defn ident (x) (x))
// (defn foobar (x y) (* (ident x) y))
// (foobar 3 4)
// -- ident
// push_deref x
// -- foobar
// push_deref x
// CallFn ident
// push_deref y
// CallFn *

// (defn if-gate (x) (if x 1 2))
// 0 push x
// 1 test 3
// 2 push 1
// 3 push 2
