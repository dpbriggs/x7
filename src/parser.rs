use std::sync::Arc;

use crate::symbols::{Expr, Function, Integer, LispResult, Num, SymbolTable};
use anyhow::anyhow;
use im::{vector, Vector};

fn parse_num(input: &str) -> LispResult<(Expr, usize)> {
    let next_whitespace_or_end = input
        .chars()
        .position(|c| !(c == '.' || c.is_numeric() || c == '-')) // TODO: Handle floating patterns like 1e3
        .unwrap_or(input.len());
    let input = &input[0..next_whitespace_or_end];
    if let Ok(res) = input.parse::<Integer>() {
        return Ok((Expr::num(res), next_whitespace_or_end));
    }
    if let Ok(res) = input.parse::<Num>() {
        return Ok((Expr::num(res), next_whitespace_or_end));
    }
    Err(anyhow!("Cannot convert: \"{}\" into an int", input))
}

fn parse_symbol(input: &str) -> LispResult<(Expr, usize)> {
    if input.is_empty() || input.chars().next().unwrap().is_numeric() {
        return Err(anyhow!("Invalid symbol! {}", input));
    }
    let output_str: String = input.chars().take_while(|&c| is_symbol_char(c)).collect();
    let end_index = output_str.len();

    let res = match output_str.as_str() {
        "true" => Expr::Bool(true),
        "false" => Expr::Bool(false),
        "nil" => Expr::Nil,
        _ if output_str.contains('.') => {
            let parts = output_str
                .split('.')
                .filter(|s| !s.is_empty())
                .map(|st| st.to_string())
                .collect();
            method_call_multiple(parts)
        }
        otherwise => Expr::Symbol(otherwise.into()),
    };
    Ok((res, end_index))
}

fn method_call(method: String) -> Expr {
    let method_clone = method.clone();
    let method_fn = move |args: Vector<Expr>, sym: &SymbolTable| {
        let rec = match args[0].get_record() {
            Ok(rec) => rec,
            Err(e) => return Err(e),
        };
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
            return Expr::Symbol(method.into());
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
fn parse_string(input: &str) -> LispResult<(Expr, usize)> {
    // TODO: Clean this up
    if input.len() < 2 {
        return Err(anyhow!("Could not parse the string: {}", input));
    } else if !input.starts_with('\"') {
        return Err(anyhow!(
            "Parse string called on something that does not start with a quote: {}",
            input
        ));
    }
    let mut curr_pos = 0;
    let mut output_str = String::new();
    let mut chars_iterator = input.chars().skip(1).peekable();
    loop {
        curr_pos += 1;
        match chars_iterator.next() {
            Some(curr_char) => match (curr_char, chars_iterator.peek()) {
                ('\\', None) => return Err(anyhow!("Tried to escape, failed! {}", input)),
                ('\\', Some('\\')) => {
                    curr_pos += 1;
                    chars_iterator.next().unwrap();
                    output_str.push('\\');
                }
                ('\\', Some('n')) => {
                    curr_pos += 1;
                    chars_iterator.next().unwrap();
                    output_str.push('\n');
                }
                ('\\', Some('r')) => {
                    curr_pos += 1;
                    chars_iterator.next().unwrap();
                    output_str.push('\r');
                }
                ('\\', Some('"')) => {
                    curr_pos += 1;
                    chars_iterator.next().unwrap();
                    output_str.push('"');
                }
                ('"', _) => {
                    assert!(input.chars().nth(curr_pos) == Some('"'));
                    // advance one after that ending quote
                    curr_pos += 1;
                    break;
                }
                (c, _) => output_str.push(c),
            },
            None => break,
        }
    }
    Ok((Expr::string(output_str), curr_pos))
}

fn parse_sexp(input: &str) -> LispResult<(Expr, usize)> {
    if input.is_empty() {
        return Err(anyhow!("Attempted to parse sexp on empty string!"));
    }
    let mut char_iterator = input.chars().peekable();
    if char_iterator.next() != Some('(') {
        return Err(anyhow!(
            "Attempted to parse sexp not starting with a brace! {}",
            input
        ));
    }
    let mut curr_pos = 1;
    let mut contents = Vector::new();
    loop {
        let curr_input_slice = &input[curr_pos..];
        let next_pos = next_non_whitespace_and_comment_pos(curr_input_slice);
        for _ in 0..next_pos {
            char_iterator.next();
            curr_pos += 1;
        }
        match char_iterator.peek() {
            None => return Err(anyhow!("Unexpected end of sexp! {}", input)),
            Some(curr_char) => {
                if curr_char == &')' {
                    curr_pos += 1;
                    break;
                }
                let (next_item, new_pos) = parse_expr(&input[curr_pos..])?;
                contents.push_back(next_item);
                for _ in 0..new_pos {
                    char_iterator.next();
                }
                curr_pos += new_pos;
            }
        }
    }
    Ok((Expr::List(contents), curr_pos))
}

fn parse_dict(input: &str) -> LispResult<(Expr, usize)> {
    if input.is_empty() {
        return Err(anyhow!("Attempted to parse a dict on an empty string!"));
    }
    if !input.starts_with('{') {
        return Err(anyhow!(
            "Attempted to parse a dict from a string not starting with a curly brace! {}",
            input
        ));
    }
    let mut curr_pos = 1;
    let mut values = Vector::new();
    loop {
        if input[curr_pos..].starts_with('}') {
            curr_pos += 1;
            break;
        }
        curr_pos += next_non_whitespace_and_comment_pos(&input[curr_pos..]);
        let (key, next_pos) = parse_expr(&input[curr_pos..])?;
        values.push_back(key);
        curr_pos += next_pos;
        curr_pos += next_non_whitespace_and_comment_pos(&input[curr_pos..]);
        if !input[curr_pos..].starts_with(':') {
            return Err(anyhow!("Expected ':' when parsing dict in {}", input));
        } else {
            curr_pos += 1;
        }
        curr_pos += next_non_whitespace_and_comment_pos(&input[curr_pos..]);
        let (value, next_pos) = parse_expr(&input[curr_pos..])?;
        values.push_back(value);
        curr_pos += next_pos;
        curr_pos += next_non_whitespace_and_comment_pos(&input[curr_pos..]);
        if input[curr_pos..].starts_with('}') {
            // return Err(anyhow!("Expected dict to end with a curly brace!", input));
            curr_pos += 1;
            break;
        } else if input[curr_pos..].starts_with(',') {
            curr_pos += 1;
            curr_pos += next_non_whitespace_and_comment_pos(&input[curr_pos..]);
        } else {
            return Err(anyhow!(
                "Unexpected string \"{}\" when parsing dict in {}",
                &input[curr_pos..],
                input
            ));
        }
    }
    values.push_front(Expr::Symbol("dict".into()));
    Ok((Expr::List(values), curr_pos))
}

fn next_non_whitespace_and_comment_pos(input: &str) -> usize {
    let mut output_pos = 0;
    loop {
        let input = &input[output_pos..];
        if input.is_empty() {
            break;
        }
        let leading_char = input.chars().next().unwrap();
        if leading_char == ';' {
            output_pos += input
                .chars()
                .position(|c| c == '\n')
                .unwrap_or(input.len() - 1)
                + 1;
        } else if leading_char.is_whitespace() {
            output_pos += input.chars().take_while(|c| c.is_whitespace()).count();
        } else {
            break;
        }
    }
    output_pos
}

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

fn parse_expr(input: &str) -> LispResult<(Expr, usize)> {
    if input.is_empty() {
        return Err(anyhow!("Attempted to parse an empty input!"));
    }
    let first_char = input.chars().next().unwrap();
    let second_char_is_numeric = input
        .chars()
        .nth(1)
        .map(|c| c.is_numeric())
        .unwrap_or(false);
    let (item, next_pos) = match first_char {
        _num if first_char.is_numeric() || (first_char == '-' && second_char_is_numeric) => {
            parse_num(input)?
        }
        '"' => parse_string(input)?,
        '(' => parse_sexp(input)?,
        '{' => parse_dict(input)?,
        '#' => {
            let (inner_sexp, next_pos) = parse_sexp(&input[1..])?;
            (
                Expr::List(vector![Expr::Symbol("anon-fn-sugar".into()), inner_sexp]),
                next_pos + 1,
            )
        }
        '@' => {
            let (inner_sexp, next_pos) = parse_sexp(&input[1..])?;
            (
                inner_sexp.push_front(Expr::Symbol("partial".into()))?,
                next_pos + 1,
            )
        }

        '^' => {
            let (inner_sexp, next_pos) = parse_sexp(&input[1..])?;
            let mut list = inner_sexp.get_list()?;
            list.push_front(Expr::Symbol("tuple".into()));
            (Expr::List(list), next_pos + 1)
        }
        '\'' => {
            let (inner_sexp, next_pos) = parse_sexp(&input[1..])?;
            (Expr::Quote(inner_sexp.get_list()?), next_pos + 1)
        }
        _sym if is_symbol_char(first_char) => parse_symbol(input)?,
        otherwise => {
            return Err(anyhow!(
                "Failed to parse! Unknown prefix {} in {}",
                otherwise,
                input
            ))
        }
    };
    Ok((item, next_pos))
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
        if self.done {
            return None;
        }
        let ignored_prefix_pos = next_non_whitespace_and_comment_pos(self.input);
        self.input = &self.input[ignored_prefix_pos..];
        if self.input.is_empty() {
            self.done = true;
            return None;
        }
        let res = match parse_expr(self.input) {
            Ok((item, next_pos)) => {
                self.input = &self.input[next_pos..];
                Ok(item)
            }
            Err(e) => {
                self.done = true;
                Err(e)
            }
        };
        Some(res)
    }
}

pub fn read(s: &str) -> ExprIterator {
    ExprIterator::new(s)
}

#[cfg(test)]
mod parser_tests {
    use im::vector;

    use super::*;
    use crate::symbols::Expr;

    #[test]
    fn parse_floats() {
        assert_eq!(parse_num("1").unwrap(), (Expr::num(1), 1));
        assert_eq!(parse_num("3 hello").unwrap(), (Expr::num(3), 1));
        assert_eq!(parse_num("1.0").unwrap(), (Expr::num(1.0f32), 3));
        assert_eq!(parse_num("1.1").unwrap(), (Expr::num(1.1f32), 3));
        assert!(parse_num("ee").is_err());
    }

    #[test]
    fn parse_strings() {
        assert_eq!(
            parse_string("\"abc\"").unwrap(),
            (Expr::string("abc".to_string()), 5)
        );
        assert_eq!(
            parse_string(r#""abc""#).unwrap(),
            (Expr::string("abc".to_string()), 5)
        );

        assert_eq!(
            parse_string(r#""""#).unwrap(),
            (Expr::string("".to_string()), 2)
        );
        // "\r\n"
        assert_eq!(
            parse_string(r#""\r\n""#).unwrap(),
            (Expr::string("\r\n".to_string()), 6)
        );
        assert_eq!(
            parse_string(r#""\r\n\"hello\""#).unwrap(),
            (Expr::string("\r\n\"hello\"".to_string()), 14)
        );
        assert_eq!(
            parse_string(r#""hello" 123"#).unwrap(),
            (Expr::string("hello".to_string()), 7)
        );
    }

    #[test]
    fn test_parse_symbol() {
        assert_eq!(
            parse_symbol("symbol 123").unwrap(),
            (Expr::Symbol("symbol".into()), 6)
        );
        assert_eq!(parse_symbol("s").unwrap(), (Expr::Symbol("s".into()), 1));
        assert!(parse_symbol("123").is_err());
    }

    #[test]
    fn test_sexp() {
        let tests = [
            (
                "(1 2 3)",
                Expr::List(vector![Expr::num(1), Expr::num(2), Expr::num(3)]),
                7,
            ),
            ("()", Expr::List(vector![]), 2),
            (
                "(neato)",
                Expr::List(vector![Expr::Symbol("neato".into())]),
                7,
            ),
            (
                "(neato   (1 2))   ",
                Expr::List(vector![
                    Expr::Symbol("neato".into()),
                    Expr::List(vector![Expr::num(1), Expr::num(2),]),
                ]),
                15,
            ),
        ];
        for (text, expected, idx) in tests {
            let res = parse_sexp(text);
            let res_s = format!("{:?}", res);
            assert_eq!(
                res.expect(&format!(
                    "Could not parse {} into {}; result is {}",
                    text, expected, res_s
                )),
                (expected.clone(), idx),
            )
        }
    }

    #[test]
    fn test_parse_expr() {
        let tests = [
            (
                "(1 2 3)",
                Expr::List(vector![Expr::num(1), Expr::num(2), Expr::num(3)]),
                7,
            ),
            ("\"hello\"", Expr::string("hello".to_string()), 7),
            ("123.12   456", Expr::num(123.12), 6),
        ];
        for (text, expected, idx) in tests {
            let res = parse_expr(text);
            let res_s = format!("{:?}", res);
            assert_eq!(
                res.expect(&format!(
                    "Could not parse {} into {}; result is {}",
                    text, expected, res_s
                )),
                (expected.clone(), idx),
            )
        }
    }

    #[test]
    fn test_expr_iterator() {
        let tests = [
            (
                "123 456 \"789\"",
                vec![
                    Expr::num(123),
                    Expr::num(456),
                    Expr::string("789".to_string()),
                ],
            ),
            ("()", vec![Expr::List(vector![])]),
            (
                "(1 2 3)",
                vec![Expr::List(vector![
                    Expr::num(1),
                    Expr::num(2),
                    Expr::num(3)
                ])],
            ),
            (
                "^(1 2 3)",
                vec![Expr::Tuple(vector![
                    Expr::num(1),
                    Expr::num(2),
                    Expr::num(3)
                ])],
            ),
            (
                "'(1 2 3)",
                vec![Expr::Quote(vector![
                    Expr::num(1),
                    Expr::num(2),
                    Expr::num(3)
                ])],
            ),
            ("hello ; 3123", vec![Expr::Symbol("hello".into())]),
            (
                "123;commented text\n456 ",
                vec![Expr::num(123), Expr::num(456)],
            ),
            (";", vec![]),
            (
                "#(+ $1 $2)",
                vec![Expr::List(vector![
                    Expr::Symbol("anon-fn-sugar".into()),
                    Expr::List(vector![
                        Expr::Symbol("+".into()),
                        Expr::Symbol("$1".into()),
                        Expr::Symbol("$2".into()),
                    ])
                ])],
            ),
            (
                "(defn foo () (println \"hello\"))",
                vec![Expr::List(vector![
                    Expr::Symbol("defn".into()),
                    Expr::Symbol("foo".into()),
                    Expr::List(vector![]),
                    Expr::List(vector![
                        Expr::Symbol("println".into()),
                        Expr::string("hello".into())
                    ])
                ])],
            ),
        ];
        for (text, expected) in tests {
            let parsed: Result<Vec<Expr>, _> = ExprIterator::new(text).into_iter().collect();
            match parsed {
                Ok(output) => assert_eq!(
                    output, expected,
                    "Could not parse {} into {:?}, instead {:?} was parsed",
                    text, expected, output
                ),
                Err(e) => assert!(
                    false,
                    "Was given error message {} when trying to parse {}",
                    e, text
                ),
            };
        }
    }

    #[test]
    fn test_dict() {
        let tests = [
            ("{}", Expr::List(vector![Expr::Symbol("dict".into())]), 2),
            (
                "{1: 2}",
                Expr::List(vector![
                    Expr::Symbol("dict".into()),
                    Expr::num(1),
                    Expr::num(2),
                ]),
                6,
            ),
            (
                "{1: 2, 3 : 4,}",
                Expr::List(vector![
                    Expr::Symbol("dict".into()),
                    Expr::num(1),
                    Expr::num(2),
                    Expr::num(3),
                    Expr::num(4),
                ]),
                14,
            ),
            (
                "{\"hello\": 2, 3 : 4,}",
                Expr::List(vector![
                    Expr::Symbol("dict".into()),
                    Expr::string("hello".into()),
                    Expr::num(2),
                    Expr::num(3),
                    Expr::num(4),
                ]),
                20,
            ),
            (
                "{{}:{3:4}}",
                Expr::List(vector![
                    Expr::Symbol("dict".into()),
                    Expr::List(vector![Expr::Symbol("dict".into())]),
                    Expr::List(vector![
                        Expr::Symbol("dict".into()),
                        Expr::num(3),
                        Expr::num(4)
                    ]),
                ]),
                10,
            ),
        ];
        for (text, expected, idx) in tests {
            let res = parse_dict(text);
            let res_s = format!("{:?}", res);
            assert_eq!(
                res.expect(&format!(
                    "Could not parse {} into {}; result is {}",
                    text, expected, res_s
                )),
                (expected.clone(), idx),
            )
        }
    }
}
