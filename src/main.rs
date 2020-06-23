mod cli;
mod repl;
mod stdlib;
mod symbols;

fn main() {
    stdlib::create_stdlib_symbol_table();
    cli::read_cli();
}
