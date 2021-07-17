use crate::cli::Options;
use std::io;
use std::io::{Read, Result as IOResult, Write};

const INDENT_SIZE: usize = 4;

#[derive(Debug, PartialEq)]
enum Token<'input> {
    LeftBrace,
    RightBrace,
    Item(&'input str),
    String(&'input str),
    Comment(&'input str),
}

struct Tokenizer<'stdin> {
    input: &'stdin str,
}

impl<'stdin> Tokenizer<'stdin> {
    fn new(input: &'stdin str) -> Self {
        Self { input }
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    // TODO: Bad input
    type Item = Token<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut iter = self.input.chars().enumerate();

        let (idx, first_non_whitespace) = iter.find(|(_, c)| !c.is_whitespace())?;

        let (range_end, token) = match first_non_whitespace {
            '(' => (idx + 1, Token::LeftBrace),
            ')' => (idx + 1, Token::RightBrace),
            '"' => {
                let idx_end = iter
                    .find(|&(_, c)| c == '"') // TODO: quoted strings
                    .map(|(idx_end, _)| idx_end)
                    .unwrap_or(self.input.len());
                (idx_end + 1, Token::String(&self.input[idx + 1..idx_end]))
            }
            ';' => {
                let idx_end = iter
                    .find(|&(_, c)| c == '\n') // TODO: quoted strings
                    .map(|(idx, _)| idx + 1)
                    .unwrap_or(self.input.len());
                (idx_end, Token::Comment(&self.input[idx..idx_end]))
            }
            _ => {
                let idx_end = iter
                    .find(|&(_, c)| c.is_whitespace() || c == ')' || c == '(')
                    .map(|(idx_end, _)| idx_end)
                    .unwrap_or(self.input.len());
                (idx_end, Token::Item(&self.input[idx..idx_end]))
            }
        };

        self.input = &self.input[range_end..];
        Some(token)
    }
}

struct SExprWalker<'input> {
    input: &'input [Token<'input>],
}

impl<'input> SExprWalker<'input> {
    fn new(input: &'input [Token<'input>]) -> Self {
        Self { input }
    }
}

#[derive(Debug, PartialEq)]
enum BasicExpr<'input> {
    Item(&'input str),
    String(&'input str),
    Comment(&'input str),
    List(Box<[BasicExpr<'input>]>),
}

// Separator
enum SeparatorStrategy {
    Space,
    NewlineSans(usize),
    Newline,
    // Bind,
}

impl BasicExpr<'_> {
    fn get_sep(&self) -> SeparatorStrategy {
        match &self {
            BasicExpr::Comment(_) | BasicExpr::List(_) => SeparatorStrategy::Newline,
            BasicExpr::String(_) => SeparatorStrategy::Space,
            BasicExpr::Item(i) => match *i {
                "defn" | "defrecord" => SeparatorStrategy::NewlineSans(1),
                "defmethod" => SeparatorStrategy::NewlineSans(2),
                "do" | "if" | "cond" | "filter" | "foreach" | "map" | "bind" => {
                    SeparatorStrategy::Newline
                }
                // "bind" => SeparatorStrategy::Bind,
                _ => SeparatorStrategy::Space,
            },
        }
    }
}

fn get_sexp<'a>(input: &[Token<'a>]) -> (usize, Box<[BasicExpr<'a>]>) {
    assert_eq!(input[0], Token::LeftBrace);
    let mut buf = Vec::new();
    let mut index = 1;
    while index < input.len() {
        let token = &input[index];
        match token {
            Token::Item(i) => buf.push(BasicExpr::Item(i)),
            Token::String(i) => buf.push(BasicExpr::String(i)),
            Token::Comment(i) => buf.push(BasicExpr::Comment(i)),
            Token::RightBrace => return (index + 1, buf.into_boxed_slice()),
            Token::LeftBrace => {
                let (idx, sexp) = get_sexp(&input[index..]);
                buf.push(BasicExpr::List(sexp));
                index += idx;
                continue;
            }
        }
        index += 1;
    }
    (index, buf.into_boxed_slice())
}

impl<'input> Iterator for SExprWalker<'input> {
    type Item = BasicExpr<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        let (end, token) = match self.input.get(0)? {
            Token::LeftBrace => {
                let (idx, sexp) = get_sexp(self.input);
                (idx, BasicExpr::List(sexp))
            }
            Token::Item(i) => (1, BasicExpr::Item(i)),
            Token::String(i) => (1, BasicExpr::String(i)),
            Token::Comment(i) => (1, BasicExpr::Comment(i)),
            Token::RightBrace => panic!("Called SExprWalker with RightBrace as first!"),
        };
        self.input = &self.input[end..];
        Some(token)
    }
}

fn leftpad<W: Write>(out: &mut W, indent_level: usize) -> IOResult<()> {
    for _ in 0..indent_level * INDENT_SIZE {
        write!(out, " ")?;
    }
    Ok(())
}

fn format_sexp<W: Write>(sexp: &BasicExpr, out: &mut W, indent_level: usize) -> IOResult<()> {
    leftpad(out, indent_level)?;
    match sexp {
        BasicExpr::Item(i) => write!(out, "{}", i)?,
        BasicExpr::Comment(i) => writeln!(out, "{}", i)?,
        BasicExpr::String(i) => write!(out, "\"{}\"", i)?,
        BasicExpr::List(l) => {
            write!(out, "(")?;
            if l.is_empty() {
                write!(out, ")")?;
                return Ok(());
            }
            let (head, tail) = l.split_first().unwrap();
            format_sexp(head, out, 0)?;
            match head.get_sep() {
                SeparatorStrategy::Newline => {
                    for i in tail {
                        writeln!(out)?;
                        format_sexp(i, out, indent_level + 1)?;
                    }
                }
                SeparatorStrategy::NewlineSans(num) => {
                    for i in &tail[0..num] {
                        write!(out, " ")?;
                        format_sexp(i, out, 0)?;
                    }
                    for i in &tail[num..] {
                        writeln!(out)?;
                        format_sexp(i, out, indent_level + 1)?;
                    }
                }
                SeparatorStrategy::Space => {
                    for i in tail {
                        write!(out, " ")?;
                        format_sexp(i, out, 0)?;
                    }
                } // SeperatorStrategy::Bind => {
                  //     // Bind looks like
                  //     // (bind
                  //     //   (a b))
                  // }
            }
            write!(out, ")")?;
            // if head.is_function_decl() {
            //     if head.is_named_function_decl() {
            //         write!(out, "defn {}", tail[0].get_item())?;
            //     } else {
            //         write!(out, "fn")?;
            //     }
            //     indent_level += 1;
            //     leftpad(out, indent_level);
            //     for t in &tail[1..] {
            //         write!(out, "\n")?;
            //         format_sexp(t, out, indent_level);
            //     }
            //     tail = &[];
            // } else {
            //     write!(out, "{}", head.get_item())?;
            // }
            // let sep = head.get_sep();
            // for i in tail {
            //     write!(out, "{}", sep)?;
            //     if sep == '\n' {
            //         format_sexp(i, out, indent_level + 1)?;
            //     } else {
            //         format_sexp(i, out, 0)?;
            //     }
            // }
        }
    }
    Ok(())
}

fn format_string<W: Write>(input: &str, out: &mut W) -> IOResult<()> {
    let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
    for sexp in SExprWalker::new(&tokens) {
        format_sexp(&sexp, out, 0)?;
        write!(out, "\n\n")?;
    }
    Ok(())
}

pub fn format(_opt: &Options) -> Result<(), i32> {
    // TODO: File input
    let mut buf = Vec::new();
    io::stdin()
        .lock()
        .read_to_end(&mut buf)
        .map_err(|e| e.raw_os_error().unwrap_or(1))?;
    let buf = String::from_utf8_lossy(&buf);
    let mut out = io::stdout();
    format_string(&buf, &mut out).unwrap();

    // println!("{}", buf);
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::formatter::BasicExpr;

    use super::{SExprWalker, Token, Tokenizer};

    #[test]
    fn can_tokenize_strings() {
        let input = r#"(+ "hello" "world")"#;
        let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
        assert_eq!(
            &tokens,
            &[
                Token::LeftBrace,
                Token::Item("+"),
                Token::String("hello"),
                Token::String("world"),
                Token::RightBrace,
            ]
        )
    }

    #[test]
    fn can_tokenize_basic() {
        let input = "33 32";
        let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
        assert_eq!(&tokens, &[Token::Item("33"), Token::Item("32"),])
    }

    #[test]
    fn can_tokenize() {
        let input = "(+ 122222      1)";
        let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
        assert_eq!(
            &tokens,
            &[
                Token::LeftBrace,
                Token::Item("+"),
                Token::Item("122222"),
                Token::Item("1"),
                Token::RightBrace,
            ]
        )
    }

    #[test]
    fn can_sexp_basic() {
        let input = "32 33";
        let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
        let sexps: Vec<BasicExpr> = SExprWalker::new(&tokens).into_iter().collect();
        assert_eq!(&sexps, &[BasicExpr::Item("32"), BasicExpr::Item("33")]);
    }

    #[test]
    fn can_sexp() {
        let input = "(+ 1 1 (+ 2 2)) (+ 2 1) 32";
        let tokens: Vec<Token> = Tokenizer::new(input).into_iter().collect();
        let sexps: Vec<BasicExpr> = SExprWalker::new(&tokens).into_iter().collect();

        assert_eq!(
            &sexps,
            &[
                BasicExpr::List(
                    vec![
                        BasicExpr::Item("+"),
                        BasicExpr::Item("1"),
                        BasicExpr::Item("1"),
                        BasicExpr::List(
                            vec![
                                BasicExpr::Item("+"),
                                BasicExpr::Item("2"),
                                BasicExpr::Item("2"),
                            ]
                            .into_boxed_slice()
                        )
                    ]
                    .into_boxed_slice(),
                ),
                BasicExpr::List(
                    vec![
                        BasicExpr::Item("+"),
                        BasicExpr::Item("2"),
                        BasicExpr::Item("1"),
                    ]
                    .into_boxed_slice()
                ),
                BasicExpr::Item("32")
            ]
        )
    }
}
