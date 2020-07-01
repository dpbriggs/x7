use crate::symbols::{Expr, LispResult, Num, ProgramError};

use nom::bytes::complete::escaped;
use nom::{
    branch::alt,
    bytes::complete::tag,
    bytes::complete::take_while1,
    character::complete::{char, multispace0, none_of},
    combinator::{cut, map, map_res},
    error::{context, VerboseError},
    multi::many0,
    number::complete::recognize_float,
    sequence::{delimited, preceded},
    IResult, Parser,
};

#[inline]
fn is_symbol_char(c: char) -> bool {
    match c {
        '(' | ')' => false,
        '"' => false,
        '\'' => false,
        ' ' => false,
        sym => !sym.is_whitespace(),
    }
}

fn parse_symbol<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    map(take_while1(is_symbol_char), |sym: &str| {
        Expr::Symbol(sym.into())
    })(i)
}

fn parse_string<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    let esc = escaped(none_of("\\\""), '\\', tag("\""));
    let esc_or_empty = alt((esc, tag("")));

    map(delimited(tag("\""), esc_or_empty, tag("\"")), |s: &str| {
        Expr::String(s.into())
    })(i)
}

fn parse_bool<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    alt((
        map(tag("true"), |_| Expr::Bool(true)),
        map(tag("false"), |_| Expr::Bool(false)),
    ))(i)
}

// TODO: Quote
fn parse_quote<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    // this should look very straight-forward after all we've done:
    // we find the `'` (quote) character, use cut to say that we're unambiguously
    // looking for an s-expression of 0 or more expressions, and then parse them
    map(
        context("quote", preceded(tag("'"), cut(s_exp(many0(parse_expr))))),
        |exprs| Expr::Quote(exprs.into()),
    )(i)
}

fn parse_num<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
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
        preceded(multispace0, inner),
        context("closing paren", cut(preceded(multispace0, char(')')))),
    )
}

fn parse_list<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    let application_inner = map(many0(parse_expr), |l| Expr::List(l.into()));
    // finally, we wrap it in an s-expression
    s_exp(application_inner)(i)
}

fn parse_expr<'a>(i: &'a str) -> IResult<&'a str, Expr, VerboseError<&'a str>> {
    preceded(
        multispace0,
        alt((
            parse_list,
            parse_quote,
            parse_string,
            parse_num,
            parse_bool,
            parse_symbol,
        )),
    )(i)
}

pub(crate) struct ExprIterator<'a> {
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
                return Some(Err(ProgramError::FailedToParse(e.to_string())));
            }
        };
        self.input = rest;
        Some(Ok(res))
    }
}

pub(crate) fn read(s: &str) -> ExprIterator {
    ExprIterator::new(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_floats() {
        assert_eq!(parse_num("1").unwrap(), ("", Expr::Num(1.0)));
        assert_eq!(parse_num("1.0").unwrap(), ("", Expr::Num(1.0)));
        assert_eq!(parse_num("1.1").unwrap(), ("", Expr::Num(1.1)));
        assert_eq!(parse_num("-1.1").unwrap(), ("", Expr::Num(-1.1)));
        assert_eq!(parse_num("-0.1").unwrap(), ("", Expr::Num(-0.1)));
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
        assert_eq!(parse_expr("1").unwrap(), ("", Expr::Num(1.0)));
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

        use im::vector;
        assert_eq!(
            parse_expr("(+ 1 1)").unwrap(),
            (
                "",
                Expr::List(vector![
                    Expr::Symbol("+".into()),
                    Expr::Num(1.0),
                    Expr::Num(1.0)
                ])
            )
        )
    }
}
