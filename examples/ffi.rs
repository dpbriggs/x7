use std::sync::Arc;

use x7::ffi::{ExprHelper, ForeignData, IntoX7Function, X7Interpreter};
use x7::symbols::Expr;

// This example shows how to use x7's FFI interface.
// The usual steps are:
// 1. Having a compatible error type
// 2. Implementing ForeignData to map from your datatype to x7's Expr and back
// 3. Adding functions to the interpreter in terms of your datatype
// 4. Setting up the interpreter and running programs

// Step 1: Setup an error type. We need to be able to return
//         errors when a conversion fails.
#[derive(Debug)]
struct MyError(String);

impl std::fmt::Display for MyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for MyError {}

// Step 2: Define the data we want x7 to understand. We're going to map
//         from MyData to x7's Expr type and vice-versa.
#[derive(Debug, Clone, PartialEq)]
enum MyData {
    Int(u64),
    String(String),
}

// Step 3: Implement ForeignData for our data type.
impl ForeignData for MyData {
    fn to_x7(&self) -> Result<x7::symbols::Expr, Box<dyn std::error::Error + Send>> {
        let res = match self {
            MyData::Int(i) => Expr::Num((*i).into()),
            MyData::String(s) => Expr::string(s.to_string()),
        };
        Ok(res)
    }

    fn from_x7(expr: &x7::symbols::Expr) -> Result<Self, Box<dyn std::error::Error + Send>> {
        let res = match expr {
            Expr::Num(n) => MyData::Int(n.to_u64()?),
            Expr::Integer(n) => MyData::Int(*n as u64),
            Expr::String(s) => MyData::String(s.to_string()),
            bad_type => {
                return Err(Box::new(MyError(format!(
                    "Cannot convert {} to MyData!",
                    bad_type
                ))))
            }
        };
        Ok(res)
    }
}

// Step 4: We're going to add our own function to the interpreter
fn setup_interpreter(interpreter: &X7Interpreter) {
    // Our function is going to add two instances of MyData,
    // and ignore any further input.
    let mydata_sum = |args: Vec<MyData>| {
        let res = match (&args[0], &args[1]) {
            (MyData::Int(l), MyData::Int(r)) => MyData::Int(l + r),
            (MyData::Int(l), MyData::String(r)) => MyData::String(format!("{}{}", l, r)),
            (MyData::String(l), MyData::Int(r)) => MyData::String(format!("{}{}", l, r)),
            (MyData::String(l), MyData::String(r)) => MyData::String(format!("{}{}", l, r)),
        };
        Ok(res) // we need to return a result
    };

    // The parameters in order to add_function_ptr mean:
    // - symbol: The name of the function in the interpreter
    // - minimum_args: The minimum number of args required to run this function.
    // - function_ptr: The function pointer for the function we're making.
    interpreter.add_function_ptr("mydata-sum", 2, Arc::new(mydata_sum));
}

fn main() {
    // Make a new interpreter
    let interpreter = X7Interpreter::new();

    // Add our function to it
    setup_interpreter(&interpreter);

    // Run some programs!
    let program = "(mydata-sum 1 1)";
    let res = interpreter.run_program::<MyData>(program);
    println!("{}                 -> {:?}", program, res);
    // prints Ok(Int(2))

    // More exotic case: MyData::String + MyData::Int
    let program = "(mydata-sum \"the number is: \" 1)";
    let res = interpreter.run_program::<MyData>(program);
    println!("{} -> {:?}", program, res);
    // prints Ok(String("the number is: 1"))

    // You do in fact get the correct MyData type after running
    // the program
    assert_eq!(
        interpreter.run_program::<MyData>("(+ 1 1 1)").unwrap(),
        MyData::Int(3)
    );

    // Notice that conversions can and will fail
    let program = "(fn (x) x)";
    println!(
        "{}                       -> {:?}",
        program,
        interpreter.run_program::<MyData>(program)
    );
    // prints Err(MyError("Cannot convert Fn<+, 1, [ ]> to MyData!"))

    // As we're parameterizing run_program over some type that implements
    // ForeignData, we can run the same program and get different results.
    let program = "(+ 1 1)";
    assert_eq!(interpreter.run_program::<u64>(program).unwrap(), 2);

    // We can more functions, and use them
    let my_sum_fn = |args: Vec<u64>| args.iter().sum::<u64>();
    interpreter.add_function("my-sum", my_sum_fn.to_x7_fn());
    assert_eq!(
        interpreter.run_program::<u64>("(my-sum '(1 2 3))").unwrap(),
        6
    );

    // ... even mixing different types!
    let string_res = interpreter
        .run_program::<String>("(my-sum '(1 2 3))")
        .unwrap();
    assert_eq!(string_res, "6".to_string());
}
