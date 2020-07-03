cargo build --release

cmd='echo "'"$1\" "'| ./target/release/x7'
hyperfine "$cmd"
