mod cli;
mod iterators;
mod modules;
mod parser;
mod stdlib;
mod symbols;
use std::error::Error;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "x7", about = "x7 Programming Language")]
pub struct Options {
    #[structopt(short = "l", long)]
    hide_loading_stdlib: bool,

    files: Vec<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let opt = Options::from_args();
    let sym_table = stdlib::create_stdlib_symbol_table(&opt);
    if opt.files.is_empty() {
        cli::read_cli(&sym_table);
    } else {
        // TODO Load File
        for f in opt.files {
            modules::run_file(&f, &sym_table)?;
        }
    }
    Ok(())
}
