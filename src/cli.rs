// use crate::repl::read;
use crate::parser::read;
use crate::symbols::{Expr, SymbolTable};
use rustyline::completion::{Completer, Pair};
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::Hinter;
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{error::ReadlineError, Config, Context, EditMode, Editor};
use rustyline_derive::Helper;
use std::{borrow::Cow, fs::File};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "x7", about = "x7 Programming Language")]
pub struct Options {
    #[structopt(
        short = "l",
        long,
        help = "Show the functions loaded from the x7 stdlib"
    )]
    pub show_loading_stdlib: bool,
    pub files: Vec<String>,
    #[structopt(
        short = "e",
        long,
        help = "Execute the file(s), and then load the interpreter"
    )]
    pub load_file: bool,

    #[structopt(
        short = "no-nat",
        long,
        help = "Load the standard library written in x7. Default: false"
    )]
    pub do_not_load_native_stdlib: bool,

    #[structopt(
        short = "f",
        long = "format",
        help = "WIP: Format some incoming x7 on stdin"
    )]
    pub formatter: bool,
    #[structopt(short = "b", long = "bytecompile", help = "WIP: bytecompile")]
    pub byte_compile: bool,
    #[structopt(short = "d", long = "debugger", help = "WIP: :^)")]
    pub debugger: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            show_loading_stdlib: false,
            files: Vec::with_capacity(0),
            load_file: false,
            do_not_load_native_stdlib: false,
            formatter: false,
            byte_compile: false,
            debugger: false,
        }
    }
}

// HUGE thank you the rustyline people for providing a nice example
// for me to follow.
// https://github.com/kkawakam/rustyline/blob/master/examples/example.rs#L1

#[derive(Helper)]
struct Completions {
    sym_table: SymbolTable,
    highlighter: MatchingBracketHighlighter,
    validator: MatchingBracketValidator,
    coloured_prompt: String,
}

impl Completions {
    fn new(sym_table: SymbolTable) -> Self {
        Self {
            sym_table,
            highlighter: MatchingBracketHighlighter::new(),
            validator: MatchingBracketValidator::new(),
            coloured_prompt: ">>> ".into(),
        }
    }
}

impl Completer for Completions {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> Result<(usize, Vec<Pair>), ReadlineError> {
        if pos < line.len() || line.is_empty() {
            return Ok((pos, vec![]));
        }
        let last_sym = line
            .chars()
            .rev()
            .position(|c| c == '(' || c == ' ' || c == ')')
            .unwrap_or(pos);
        let line_fragment = &line[(pos - last_sym)..pos];
        if line_fragment.is_empty() {
            return Ok((pos, vec![]));
        }
        Ok((
            pos,
            self.sym_table
                .query_symbol_starts_with(line_fragment)
                .into_iter()
                .map(|matched| Pair {
                    display: matched.clone(),
                    replacement: matched[last_sym..].into(),
                })
                .collect(),
        ))
    }
}

impl Highlighter for Completions {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        if default {
            Cow::Borrowed(&self.coloured_prompt)
        } else {
            Cow::Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Owned("\x1b[1m".to_owned() + hint + "\x1b[m")
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for Completions {
    fn validate(
        &self,
        ctx: &mut validate::ValidationContext,
    ) -> rustyline::Result<validate::ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

impl Hinter for Completions {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, _ctx: &rustyline::Context<'_>) -> Option<Self::Hint> {
        if pos < line.len() || line.is_empty() {
            return None;
        }
        let last_sym = line
            .chars()
            .rev()
            .position(|c| c == '(' || c == ' ' || c == ')')
            .unwrap_or(pos);
        let line_fragment = &line[(pos - last_sym)..pos];
        if line_fragment.is_empty() {
            return None;
        }
        self.sym_table
            .query_symbol_starts_with(line_fragment)
            .into_iter()
            .next()
            .map(|s| s[last_sym..].to_owned())
    }
}

pub fn read_cli(sym_table: &SymbolTable) {
    let conf = Config::builder()
        .edit_mode(EditMode::Emacs)
        .auto_add_history(true)
        .indent_size(2)
        .tab_stop(2)
        .build();
    // TODO: Auto-complete
    let mut rl = Editor::<Completions>::with_config(conf);
    let helper = Completions::new(sym_table.clone());
    rl.set_helper(Some(helper));
    if rl.load_history("history.txt").is_err() {
        if let Err(e) = File::create("history.txt") {
            eprintln!("Attempted to create history file, but failed! {}", e);
        }
        if rl.load_history("history.txt").is_err() {
            eprintln!("Successfully created history, but could not load it!")
        }
        println!("No previous history.");
    }
    let quit_symbol = Expr::Symbol("quit".into());
    let exit_symbol = Expr::Symbol("exit".into());
    loop {
        let readline = rl.readline(">>> ");
        match readline {
            Ok(line) => {
                if line.is_empty() {
                    continue;
                }
                for expr in read(line.as_str()) {
                    let prog = match expr {
                        Ok(prog) => prog,
                        Err(e) => {
                            println!("{:?}", e);
                            continue;
                        }
                    };
                    if prog == quit_symbol || prog == exit_symbol {
                        println!("cy@");
                        return;
                    }
                    match prog.eval(sym_table) {
                        Ok(p) => println!("{:?}", p),
                        Err(e) => {
                            report_error(&e);
                            continue;
                        }
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("Bye :]");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("cy@");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

pub fn report_error(err: &anyhow::Error) {
    let first = err.chain().last().unwrap();
    println!("Error: {}\n", first);

    let mut print_stackstace = true;

    for e in err.chain().rev().skip(1) {
        if print_stackstace {
            println!("Stacktrace:");
        }
        print_stackstace = false;
        println!("  - {}", e)
    }
}
