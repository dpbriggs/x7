use crate::cli::report_error;
use structopt::StructOpt;

use x7::{cli, modules, stdlib};

fn main() -> Result<(), i32> {
    let opt = cli::Options::from_args();
    let sym_table = stdlib::create_stdlib_symbol_table(&opt);
    if opt.files.is_empty() {
        cli::read_cli(&sym_table);
    } else {
        // TODO Load File
        for f in opt.files {
            if let Err(e) = modules::run_file(&f, &sym_table) {
                report_error(&e);
                return Err(1);
            }
        }
    }
    Ok(())
}
