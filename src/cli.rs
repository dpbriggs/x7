use crate::repl::read;
use rustyline::error::ReadlineError;
use rustyline::Editor;

pub(crate) fn read_cli() {
    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        // TODO: Make the actual file
        println!("No previous history.");
    }
    loop {
        let readline = rl.readline(">>> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                let prog = match read(line.as_str()) {
                    Ok(p) => p,
                    Err(e) => {
                        println!("{:?}", e);
                        continue;
                    }
                };
                for expr in prog.top_level_iter() {
                    let res = match expr.eval() {
                        Ok(p) => p,
                        Err(e) => {
                            println!("{:?}", e);
                            continue;
                        }
                    };
                    println!("{}", res);
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
