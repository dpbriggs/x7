use std::collections::HashMap;

use anyhow::{anyhow, bail, ensure, Context};
use im::{vector, Vector};
use itertools::Itertools;

use crate::{
    bad_types, exact_len,
    parser2::read,
    symbols::{ByteCompiledFunction, Expr, LispResult, ProgramError, Symbol},
};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Label(usize);

#[derive(Debug, Clone)]
enum UnlinkedInstruction {
    Instruction(Instruction),
    Test(Label),
    JumpTo(Label),
}

pub struct ByteCodeCompiler {
    instructions: Vec<UnlinkedInstruction>,
    named_functions: Vec<(ByteCompiledFunction, Option<String>)>,
    label_map: HashMap<Label, usize>,
    label_count: usize,
}

impl Default for ByteCodeCompiler {
    fn default() -> Self {
        ByteCodeCompiler::new()
    }
}

impl ByteCodeCompiler {
    pub fn new() -> Self {
        ByteCodeCompiler {
            instructions: Vec::new(),
            named_functions: Vec::new(),
            label_map: HashMap::new(),
            label_count: 0,
        }
    }

    fn new_label(&mut self) -> Label {
        let label = self.label_count;
        self.label_count += 1;
        Label(label)
    }

    fn register_label(&mut self, label: Label) -> LispResult<()> {
        if self.label_map.contains_key(&label) {
            return Err(anyhow!("Label {:?} has already been registered!", label));
        }
        self.label_map.insert(label, self.len());
        Ok(())
    }

    fn compile_list(
        &mut self,
        sym: Option<&str>,
        head: Expr,
        args: Vector<Expr>,
    ) -> LispResult<()> {
        match sym {
            Some("cond") => {
                ensure!(args.len() % 2 == 0, ProgramError::CondBadConditionNotEven);
                let end_jmp = self.new_label();
                for (pred, body) in args.into_iter().tuples() {
                    self.compile_expr(pred)?;
                    let next_test_jump = self.new_label();
                    self.push_test(next_test_jump);
                    self.compile_expr(body)?;
                    self.push_jmp(end_jmp);
                    self.register_label(next_test_jump)?;
                }
                self.push_instruction(Instruction::Fail("Control flow reached past end of cond"));
                self.register_label(end_jmp)?;
            }
            Some("def") => {
                // TODO: Handle wrong number of args
                exact_len!(args, 2);
                let bind_sym = args[0].get_symbol()?;
                self.compile_expr(args[1].clone())?;
                self.push_instruction(Instruction::GlobalBind(bind_sym));
                self.push_nil();
            }
            Some("defn") => {
                exact_len!(args, 3, 4);
                // (defn foo "doc" (x y) (+ x y))
                let (name, doc, args, body) = if args.len() == 3 {
                    (args[0].clone(), None, args[1].clone(), args[2].clone())
                } else {
                    (
                        args[0].clone(),
                        Some(args[1].get_string()?), // TODO: Why does this eval in stdlib :thonking_eval:
                        args[2].clone(),
                        args[3].clone(),
                    )
                };
                let sym = name.get_symbol()?;
                let ff = self.compile_function(Some(sym), args, body)?;
                self.named_functions.push((ff, doc));
                self.push_nil()
                // TODO: Record the fact we have a function
            }
            Some("fn") => {
                exact_len!(args, 2);
                // (fn (x y) (+ x y))
                let ff = self.compile_function(None, args[0].clone(), args[1].clone())?;
                self.push_instruction(Instruction::Push(Expr::ByteCompiledFunction(ff)));
            }
            Some("head") => {
                exact_len!(args, 1);
                self.compile_expr(args[0].clone())?;
                self.push_instruction(Instruction::Head);
            }
            Some("tail") => {
                exact_len!(args, 1);
                for arg in args.iter().rev() {
                    self.compile_expr(arg.clone())?;
                }
                self.push_instruction(Instruction::Tail);
            }
            Some("cons") => {
                exact_len!(args, 2);
                for arg in args.iter().rev() {
                    self.compile_expr(arg.clone())?;
                }
                self.push_instruction(Instruction::Cons);
            }
            Some("+") => {
                for arg in args.iter().rev() {
                    self.compile_expr(arg.clone())?;
                }
                self.push_instruction(Instruction::Add(args.len()));
            }
            Some("breakpoint") => {
                exact_len!(args, 0);
                self.push_instruction(Instruction::BreakPoint);
                self.push_nil();
            }
            Some("map") => {
                // (map fn coll)
                dbg!(&args);
                exact_len!(args, 2);
                self.compile_expr(args[1].clone())?;
                self.compile_expr(args[0].clone())?;
                self.push_instruction(Instruction::Map);
            }
            _ => {
                for arg in args.iter().rev() {
                    self.compile_expr(arg.clone())?;
                }
                self.compile_expr(head)?;
                self.push_instruction(Instruction::CallFn(args.len()));
            }
        };
        Ok(())
    }

    fn compile_function(
        &mut self,
        sym: Option<Symbol>,
        named_args: Expr,
        body: Expr,
    ) -> LispResult<ByteCompiledFunction> {
        let end_of_fn = self.new_label();
        self.push_jmp(end_of_fn);
        let start_loc = self.len();
        let arg_symbols: Vec<Symbol> = named_args
            .get_list()?
            .into_iter()
            .map(|e| e.get_symbol())
            .collect::<Result<_, _>>()?;
        let minimum_args = arg_symbols.len();
        self.push_instruction(Instruction::EnterScope);
        for arg_sym in arg_symbols.iter().copied() {
            self.push_instruction(Instruction::LocalScopeBind(arg_sym));
        }
        self.compile_expr(body)?;
        self.push_instruction(Instruction::ExitScope);
        self.push_instruction(Instruction::Ret);
        let name = match sym {
            Some(s) => s,
            None => "AnonByteCompiledFn".into(),
        };
        let ff = ByteCompiledFunction::new(
            name,
            minimum_args,
            arg_symbols.into_boxed_slice(),
            start_loc,
        );
        self.register_label(end_of_fn)?;
        Ok(ff)
    }

    fn push_jmp(&mut self, label: Label) {
        self.instructions.push(UnlinkedInstruction::JumpTo(label))
    }

    fn push_test(&mut self, label: Label) {
        self.instructions.push(UnlinkedInstruction::Test(label))
    }

    fn push_nil(&mut self) {
        self.push_instruction(Instruction::Push(Expr::Nil));
    }

    fn push_instruction(&mut self, inst: Instruction) {
        self.instructions
            .push(UnlinkedInstruction::Instruction(inst))
    }

    fn len(&self) -> usize {
        self.instructions.len()
    }

    fn compile_expr(&mut self, e: Expr) -> LispResult<()> {
        if let Expr::List(l) = e {
            if l.is_empty() {
                self.push_instruction(Instruction::Push(Expr::List(vector![])));
                return Ok(());
            }
            let head = &l[0];
            match head {
                Expr::Symbol(sym) => {
                    let sym_str = sym.to_string();
                    self.compile_list(Some(&sym_str), head.clone(), l.skip(1))?;
                }
                Expr::List(_) => {
                    self.compile_list(None, head.clone(), l.skip(1))?;
                }
                _ => return bad_types!("uh oh"),
            };
        } else {
            self.push_instruction(Instruction::Push(e));
        }
        Ok(())
    }

    fn link(&mut self) -> LispResult<Vec<Instruction>> {
        self.push_instruction(Instruction::Halt);
        let mut output = Vec::with_capacity(self.instructions.len());
        for instruction in self.instructions.iter().cloned() {
            match instruction {
                UnlinkedInstruction::Instruction(inst) => output.push(inst),
                UnlinkedInstruction::JumpTo(label) => {
                    let dest = self
                        .label_map
                        .get(&label)
                        .ok_or_else(|| anyhow!("Unknown label {:?}", label))?;
                    output.push(Instruction::Jump(*dest));
                }
                UnlinkedInstruction::Test(label) => {
                    let dest = self
                        .label_map
                        .get(&label)
                        .ok_or_else(|| anyhow!("Unknown label {:?}", label))?;
                    output.push(Instruction::Test(*dest));
                }
            }
        }
        Ok(output)
    }
    #[allow(clippy::type_complexity)]
    pub fn compile(
        &mut self,
        input: &str,
    ) -> LispResult<(
        Vec<Instruction>,
        Vec<(ByteCompiledFunction, Option<String>)>,
    )> {
        for expr in read(input) {
            self.compile_expr(expr?)?;
            // self.push_instruction(Instruction::Pop);
        }
        let instructions = self.link()?;
        Ok((instructions, self.named_functions.clone()))
    }
}

use super::bytecode_vm::Instruction;

// pub fn byte_compile(input: &str) -> LispResult<Vec<Instruction>> {
//     let mut compiler = ByteCodeCompiler::new();
//     for expr in read(input) {
//         let expr = expr?;
//         dbg!(&expr);
//         compiler.compile_expr(expr)?;
//         compiler.print_internals();
//     }
//     Ok(())
// }
