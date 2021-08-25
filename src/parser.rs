use crate::symbols::{Expr, LispResult, Num, ProgramError};

// s-expression parser using nom.
// Supports the usual constructs (quotes, numbers, strings, comments)

// HUGE thanks to the nom people (Geal, adamnemecek, MarcMcCaskey, et all)
// who had an s_expression example for me to work from.
// https://github.com/Geal/nom/blob/master/examples/s_expression.rs

use crate::symbols::Function;
use nom::bytes::complete::escaped;
use nom::{
    branch::alt,
    bytes::complete::tag,
    bytes::complete::{take_till, take_while1},
    character::complete::{char, multispace0, none_of},
    combinator::{cut, map, map_res},
    error::{context, VerboseError},
    multi::{many0, many1},
    number::complete::recognize_float,
    sequence::{delimited, preceded},
    IResult, Parser,
};
use std::sync::Arc;

#[inline]
fn is_symbol_char(c: char) -> bool {
    match c {
        '(' | ')' => false,
        '"' => false,
        '\'' => false,
        ';' => false,
        ' ' => false,
        sym => !sym.is_whitespace(),
    }
}

use crate::symbols::SymbolTable;
use im::Vector;

fn method_call(method: String) -> Expr {
    let method_clone = method.clone();
    let method_fn = move |args: Vector<Expr>, sym: &SymbolTable| {
        let rec = match args[0].get_record() {
            Ok(rec) => rec,
            Err(e) => return Err(e),
        };
        use crate::records::Record;
        rec.call_method(&method_clone, args.clone().slice(1..), sym)
    };
    let f = Function::new(
        format!("method_call<{}>", method),
        1,
        Arc::new(method_fn),
        true,
    );
    Expr::function(f)
}

/// Massage a symbol like `Record.field.inner_field`
/// into (.inner_field (.field Record))
///
/// If there's left hand side, like `.read_to_string`,
/// return a `Fn<method_call<read_to_string>>` instead.
fn method_call_multiple(methods: Vec<String>) -> Expr {
    if methods.len() == 1 {
        return method_call(methods[0].clone());
    }
    let ff: Expr = methods.into_iter().fold(Expr::Nil, |acc, method| {
        if matches!(acc, Expr::Nil) {
            return Expr::Symbol(method);
        }
        let acc_clone = acc.clone();
        let method_clone = method.clone();
        let method_fn = move |args: Vector<Expr>, sym: &SymbolTable| {
            let mut args = args;
            // Stick the acc at the front
            args.push_front(acc.clone());
            let rec = match args[0].eval(sym).and_then(|e| e.get_record()) {
                Ok(rec) => rec,
                Err(e) => return Err(e),
            };
            use crate::records::Record;
            rec.call_method(&method_clone, args.slice(1..), sym)
        };
        let f = Function::new(
            format!("method_call<{}; {}>", method, acc_clone),
            0,
            Arc::new(method_fn),
            true,
        );
        Expr::List(im::Vector::unit(Expr::function(f)))
    });
    ff
}

fn parse_symbol(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(take_while1(is_symbol_char), |sym: &str| {
        if sym.contains('.') {
            let methods = sym
                .split('.')
                .filter(|s| !s.is_empty())
                .map(|st| st.to_string())
                .collect();
            method_call_multiple(methods)
        } else {
            Expr::Symbol(sym.into())
        }
    })(i)
}

fn decode_control_character_str(input: &str) -> String {
    let mut output_str = String::new();
    if input.is_empty() {
        return output_str;
    }
    let mut skip_next_c = false;
    for (first_c, second_c) in input.chars().zip(input.chars().skip(1)) {
        if skip_next_c {
            skip_next_c = false;
            continue;
        }
        if first_c == '\\' {
            skip_next_c = true;
            match second_c {
                'n' => output_str.push('\n'),
                'r' => output_str.push('\r'),
                _ => {
                    skip_next_c = false;
                }
            }
        } else {
            output_str.push(first_c);
        }
    }
    output_str.push(input.chars().last().unwrap());
    output_str
}

fn parse_string(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let esc = escaped(none_of("\\\""), '\\', none_of(""));
    // let esc = escaped(none_of("\\\""), '\\', one_of(r#"n"\"#));
    let esc_or_empty = alt((esc, tag("")));

    map(delimited(tag("\""), esc_or_empty, tag("\"")), |s: &str| {
        Expr::String(decode_control_character_str(s))
    })(i)
}

fn parse_bool(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    alt((
        map(tag("true"), |_| Expr::Bool(true)),
        map(tag("false"), |_| Expr::Bool(false)),
    ))(i)
}

fn ignored_input(i: &str) -> IResult<&str, &str, VerboseError<&str>> {
    let comment_parse = delimited(
        preceded(multispace0, tag(";")),
        take_till(|c| c == '\n'),
        multispace0,
    );
    let comment_parse = many1(comment_parse).map(|_| "");
    alt((comment_parse, multispace0))(i)
}

fn parse_tuple(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let make_tuple = |exprs: Vec<_>| {
        let mut tuple_list = im::Vector::unit(Expr::Symbol("tuple".into()));
        tuple_list.append(exprs.into());
        Expr::List(tuple_list)
    };
    map(
        context("quote", preceded(tag("^"), cut(s_exp(many0(parse_expr))))),
        make_tuple,
    )(i)
}

fn parse_quote(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(
        context("quote", preceded(tag("'"), cut(s_exp(many0(parse_expr))))),
        |exprs| Expr::Quote(exprs.into()),
    )(i)
}

fn parse_num(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map_res(recognize_float, |digit_str: &str| {
        digit_str.parse::<Num>().map(Expr::Num)
    })(i)
}

fn s_exp<'a, O1, F>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O1, VerboseError<&'a str>>
where
    F: Parser<&'a str, O1, VerboseError<&'a str>>,
{
    delimited(
        char('('),
        preceded(ignored_input, inner),
        context("closing paren", cut(preceded(ignored_input, char(')')))),
    )
}

fn parse_list(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let application_inner = map(many0(parse_expr), |l| Expr::List(l.into()));
    // finally, we wrap it in an s-expression
    s_exp(application_inner)(i)
}

fn parse_expr(i: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    delimited(
        ignored_input,
        alt((
            parse_list,
            parse_quote,
            parse_tuple,
            parse_string,
            parse_num,
            parse_bool,
            parse_symbol,
        )),
        ignored_input,
    )(i)
}

pub struct ExprIterator<'a> {
    input: &'a str,
    done: bool,
}

impl<'a> ExprIterator<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self { input, done: false }
    }
}

impl<'a> Iterator for ExprIterator<'a> {
    type Item = LispResult<Expr>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.input.is_empty() {
            return None;
        }
        let (rest, res) = match parse_expr(self.input) {
            Ok(r) => r,
            Err(e) => {
                self.done = true;
                return Some(Err(anyhow::Error::new(ProgramError::FailedToParse(
                    e.to_string(),
                ))));
            }
        };
        self.input = rest;
        Some(Ok(res))
    }
}

pub fn read(s: &str) -> ExprIterator {
    ExprIterator::new(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bigdecimal::{BigDecimal, FromPrimitive};

    macro_rules! num_f {
        ($n:expr) => {
            Expr::Num(BigDecimal::from_f64($n).unwrap())
        };
    }

    #[test]
    fn parse_floats() {
        assert_eq!(parse_num("1").unwrap(), ("", num_f!(1.0)));
        assert_eq!(parse_num("1.0").unwrap(), ("", num_f!(1.0)));
        assert_eq!(parse_num("1.1").unwrap(), ("", num_f!(1.1)));
        assert_eq!(parse_num("-1.1").unwrap(), ("", num_f!(-1.1)));
        assert_eq!(parse_num("-0.1").unwrap(), ("", num_f!(-0.1)));
    }

    macro_rules! test_symbol {
        ($($sym:literal),*) => {
            $(
                assert_eq!(
                    parse_symbol($sym).unwrap(),
                    ("", Expr::Symbol($sym.into()))
                );
            )*
        }
    }

    #[test]
    fn parse_sym() {
        test_symbol!("abc", "abc1", "empty?", "test", "foo-bar", "-foobar");
    }

    // TODO: Make this way less brittle
    #[test]
    fn parse_str() {
        assert_eq!(
            parse_string(r#""1""#).unwrap(),
            ("", Expr::String("1".into()))
        );

        assert_eq!(
            parse_string(r#""""#).unwrap(),
            ("", Expr::String("".into()))
        );

        assert_eq!(
            parse_string(r#""hello-world""#).unwrap(),
            ("", Expr::String("hello-world".into()))
        );

        assert_eq!(
            parse_string(r#""hello world""#).unwrap(),
            ("", Expr::String("hello world".into()))
        );

        assert_eq!(
            parse_string(r#""hello? world""#).unwrap(),
            ("", Expr::String("hello? world".into()))
        );
    }

    #[test]
    fn parse_ex() {
        assert_eq!(parse_expr("1").unwrap(), ("", num_f!(1.0)));
        assert_eq!(
            parse_expr(r#""hello? world""#).unwrap(),
            ("", Expr::String("hello? world".into()))
        );
        assert_eq!(
            parse_expr(r#""1""#).unwrap(),
            ("", Expr::String("1".into()))
        );

        assert_eq!(parse_expr(r#""""#).unwrap(), ("", Expr::String("".into())));

        assert_eq!(
            parse_expr(r#""hello-world""#).unwrap(),
            ("", Expr::String("hello-world".into()))
        );

        assert_eq!(
            parse_expr(r#""hello world""#).unwrap(),
            ("", Expr::String("hello world".into()))
        );

        assert_eq!(
            parse_expr(r#""hello? world""#).unwrap(),
            ("", Expr::String("hello? world".into()))
        );

        assert_eq!(parse_expr("; hello\n\n\n1").unwrap(), ("", num_f!(1.0)));
        assert_eq!(parse_expr("1 ; hello").unwrap(), ("", num_f!(1.0)));

        use im::vector;
        assert_eq!(
            parse_expr("(+ 1 1)").unwrap(),
            (
                "",
                Expr::List(vector![Expr::Symbol("+".into()), num_f!(1.0), num_f!(1.0)])
            )
        )
    }

    #[test]
    fn parse_ignored_input() {
        assert_eq!(ignored_input("; hello\n"), Ok(("", "")));
        assert_eq!(ignored_input("; hello"), Ok(("", "")));
        assert_eq!(ignored_input(";hello"), Ok(("", "")));
        assert_eq!(ignored_input(" ; hello"), Ok(("", "")));
    }

    #[test]
    fn test_expr_iterator() {
        let mut iter = ExprIterator::new("1 ; hello");
        let next = iter.next();
        assert!(next.is_some());
        assert_eq!(next.unwrap().unwrap(), num_f!(1.0));
        assert!(iter.next().is_none());
    }
}
