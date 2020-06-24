mod cli;
mod repl;
mod stdlib;
mod symbols;

fn main() {
    let sym_table = stdlib::create_stdlib_symbol_table();
    cli::read_cli(&sym_table);
}
