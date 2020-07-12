use std::error::Error;
use structopt::StructOpt;

use x7::{cli, modules, stdlib};

fn main() -> Result<(), Box<dyn Error>> {
    let opt = cli::Options::from_args();
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
