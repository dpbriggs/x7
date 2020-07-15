use crate::cli::Options;
use crate::parser::read;
use crate::symbols::SymbolTable;
use std::error::Error;
use std::fs::File;
use std::io;
use std::io::prelude::*;

// TODO: Figure out best way to have the stdlib available
// $X7_PATH?
fn stdlib_dir() -> io::Result<&'static str> {
    Ok("./stdlib")
}

use glob::glob;

pub(crate) fn load_x7_stdlib(
    opts: &Options,
    symbol_table: &SymbolTable,
) -> Result<(), Box<dyn Error>> {
    let path = format!("{}/**/*.x7", stdlib_dir()?);
    for entry in glob(&path)? {
        let entry = entry?;
        let mut strbuf = String::new();
        File::open(entry)?.read_to_string(&mut strbuf)?;
        for expr in read(strbuf.as_str()) {
            let prog = match expr {
                Ok(prog) => prog,
                Err(e) => {
                    println!("{:?}", e);
                    continue;
                }
            };
            match prog.eval(symbol_table) {
                Ok(p) => {
                    if !opts.hide_loading_stdlib {
                        println!("{}", p);
                    }
                }
                Err(e) => {
                    println!("{:?}", e);
                    continue;
                }
            }
        }
    }
    Ok(())
}

pub fn run_file(file_name: &str, symbol_table: &SymbolTable) -> Result<i32, Box<dyn Error>> {
    let mut strbuf = String::new();
    File::open(file_name)?.read_to_string(&mut strbuf)?;
    for expr in read(strbuf.as_str()) {
        let prog = expr?;
        prog.eval(symbol_table)?;
    }
    Ok(0)
}
