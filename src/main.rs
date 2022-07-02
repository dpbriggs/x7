#![allow(clippy::unnecessary_wraps)]

use crate::cli::report_error;
use structopt::StructOpt;

use x7::{cli, formatter, modules, stdlib, vm::ByteCodeVM};

fn main() -> Result<(), i32> {
    let opt = cli::Options::from_args();
    let mut sym_table = stdlib::create_stdlib_symbol_table(&opt);
    if opt.formatter {
        return formatter::format(&opt);
    }
    if opt.files.is_empty() {
        cli::read_cli(&sym_table, opt.byte_compile);
    } else {
        for f in opt.files {
            if opt.byte_compile {
                let contents = std::fs::read_to_string(&f).expect("Failed to read file");
                if let Err(e) = ByteCodeVM::new(sym_table, opt.debugger).run(&contents) {
                    report_error(&e);
                    return Err(1);
                }
                return Ok(());
            }
            if let Err(e) = modules::run_file(&f, &sym_table) {
                report_error(&e);
                return Err(1);
            }
        }
        if opt.load_file {
            cli::read_cli(&sym_table, opt.byte_compile);
        }
    }
    sym_table.wait_on_threads();
    Ok(())
}
