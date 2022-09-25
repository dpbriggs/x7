use criterion::{black_box, criterion_group, criterion_main, Criterion};
use x7::parser2::read;
use x7::stdlib;

fn parse_benchmark(c: &mut Criterion) {
    let program = "(doall (take 100 (map fib (range)))) (+ 1 1)";
    c.bench_function("parse doall", |b| {
        b.iter(|| {
            for i in read(&program) {
                black_box(i.unwrap());
            }
        })
    });
}

fn eval_benchmark(c: &mut Criterion) {
    let program = "(doall (take 100 (map fib (range)))) (+ 1 1)";
    let sym_table = stdlib::create_stdlib_symbol_table_no_cli();
    c.bench_function("parse doall", |b| {
        b.iter(|| {
            for i in read(&program) {
                let prog = i.unwrap();
                black_box(prog.eval(&sym_table).unwrap());
            }
        })
    });
}

criterion_group!(name = benches;
                 config = Criterion::default().sample_size(75);
                 targets = parse_benchmark, eval_benchmark);
criterion_main!(benches);
