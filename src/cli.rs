// use crate::repl::read;
use crate::parser::read;
use crate::symbols::SymbolTable;
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "x7", about = "x7 Programming Language")]
pub struct Options {
    #[structopt(short = "l", long)]
    pub hide_loading_stdlib: bool,
    pub files: Vec<String>,
}

pub fn read_cli(sym_table: &SymbolTable) {
    let conf = Config::builder().auto_add_history(true).build();
    // TODO: Auto-complete
    let mut rl = Editor::<()>::with_config(conf);
    if rl.load_history("history.txt").is_err() {
        // TODO: Make the actual file
        println!("No previous history.");
    }
    loop {
        let readline = rl.readline(">>> ");
        match readline {
            Ok(line) => {
                if line == "" {
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
