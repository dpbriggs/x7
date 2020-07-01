use crate::parser::read;
use crate::symbols::SymbolTable;
use std::error::Error;
use std::fs::File;
use std::io;
use std::io::prelude::*;

fn stdlib_dir() -> io::Result<&'static str> {
    Ok("./stdlib")
}

use glob::glob;

pub(crate) fn load_x7_stdlib(symbol_table: &SymbolTable) -> Result<(), Box<dyn Error>> {
    let path = format!("{}/**/*.x7", stdlib_dir()?);
    dbg!(&symbol_table);
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
                Ok(p) => println!("{}", p),
                Err(e) => {
                    println!("{:?}", e);
                    continue;
                }
            }
        }
    }
    Ok(())
}
