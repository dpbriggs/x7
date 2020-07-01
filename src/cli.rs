// use crate::repl::read;
use crate::parser::read;
use crate::symbols::SymbolTable;
use rustyline::error::ReadlineError;
use rustyline::Editor;

pub(crate) fn read_cli(sym_table: &SymbolTable) {
    let mut rl = Editor::<()>::new();
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
                rl.add_history_entry(line.as_str());
                for expr in read(line.as_str()) {
                    let prog = match expr {
                        Ok(prog) => prog,
                        Err(e) => {
                            println!("{:?}", e);
                            continue;
                        }
                    };
                    match prog.eval(sym_table) {
                        Ok(p) => println!("{}", p),
                        Err(e) => {
                            println!("{:?}", e);
                            continue;
                        }
                    }
                }
                // let prog = match read(line.as_str()) {
                //     Ok(p) => p,
                //     Err(e) => {
                //         println!("{:?}", e);
                //         continue;
                //     }
                // };
                // dbg!(&prog);
                // match prog.eval(sym_table) {
                //     Ok(p) => println!("{}", p),
                //     Err(e) => {
                //         println!("{:?}", e);
                //         continue;
                //     }
                // };
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
