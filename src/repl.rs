use crate::symbols::{Expr, LispResult, ProgramError};

// TODO: Non scuffed parsing

fn find_matching(s: &str) -> LispResult<usize> {
    // s: (...)
    assert!(s.starts_with('('));
    let mut count = 1;
    let mut in_str = false;
    for (pos, c) in s.chars().enumerate().skip(1) {
        if in_str && c != '"' {
            continue;
        }
        match c {
            '"' => {
                in_str = !in_str;
            }
            '(' => {
                count += 1;
            }
            ')' => {
                count -= 1;
                if count == 0 {
                    return Ok(pos);
                }
            }
            _ => continue,
        };
    }
    Err(ProgramError::UnexpectedEOF)
    // panic!("failed to parse!");
}

fn read_int(s: &str) -> LispResult<(Expr, usize)> {
    let mut periods_seen = 0;
    let mut end_pos = 0;
    let (is_neg, s) = if s.starts_with('-') {
        (-1.0, &s[1..])
    } else {
        (1.0, s)
    };
    for c in s.chars() {
        match c {
            '0'..='9' => {
                end_pos += 1;
                continue;
            }
            '.' => {
                periods_seen += 1;
                end_pos += 1;
                continue;
            }
            ' ' => {
                break;
            }
            sym => {
                if sym.is_ascii_whitespace() || sym == '\n' {
                    break;
                } else {
                    return Err(ProgramError::FailedToParseInt);
                }
            }
        };
    }
    if periods_seen > 1 {
        println!("here");
        return Err(ProgramError::FailedToParseInt);
    }
    let num: f64 = is_neg
        * s[..end_pos].parse::<f64>().map_err(|e| {
            println!("{}", e);
            ProgramError::FailedToParseInt
        })?;
    Ok((Expr::Num(num), end_pos + 1))
}

fn read_str(s: &str) -> LispResult<(Expr, usize)> {
    assert!(s.starts_with('"'));
    s[1..]
        .find('"')
        .map(|end_pos| Ok((Expr::String(s[1..=end_pos].into()), end_pos + 2)))
        .unwrap_or(Err(ProgramError::FailedToParseString))
}

fn read_word(s: &str) -> LispResult<(Expr, usize)> {
    if s.is_empty() {
        return Err(ProgramError::UnexpectedEOF);
    }
    let end = s.find(' ').unwrap_or_else(|| s.len()); // TODO: Fix strings in words
    let string = s[..end].to_string().trim_end().to_string();
    Ok((Expr::Symbol(string), end + 1))
}

pub(crate) fn read(s: &str) -> LispResult<Expr> {
    // assert!(s.starts_with('('));
    if s.is_empty() {
        return Ok(Expr::Nil);
    }
    let mut exprs = Vec::new();
    let mut ss = s;
    while !ss.is_empty() {
        let first_char = ss.chars().next().unwrap();
        match first_char {
            '-' | '0'..='9' => {
                let (expr, new_pos) = read_int(ss)?;
                exprs.push(expr);
                let new_start = std::cmp::min(ss.len(), new_pos);
                if new_start == 0 {
                    break;
                }
                ss = &ss[new_start..];
            }
            '"' => {
                let (expr, new_pos) = read_str(ss)?;
                exprs.push(expr);
                let new_start = std::cmp::min(ss.len(), new_pos);
                if new_start == 0 {
                    break;
                }
                ss = &ss[new_start..];
            }
            'a'..='z' | 'A'..='Z' | '+' => {
                let (expr, new_pos) = read_word(ss)?;
                exprs.push(expr);
                let new_start = std::cmp::min(ss.len(), new_pos);
                if new_start == 0 {
                    break;
                }
                ss = &ss[new_start..];
            }
            '(' => {
                let end_pos = find_matching(ss)?;
                let sub_exprs = read(&ss[1..end_pos])?;
                exprs.push(sub_exprs);
                ss = &ss[end_pos + 1..];
            }
            sym => {
                if !is_symbol_char(sym) {
                    return Err(ProgramError::InvalidCharacterInSymbol);
                }
                if sym.is_ascii_whitespace() || sym == '\n' {
                    ss = &ss[1..];
                    continue;
                }
                let (expr, new_pos) = read_word(ss)?;
                exprs.push(expr);
                let new_start = std::cmp::min(ss.len(), new_pos);
                if new_start == 0 {
                    break;
                }
                ss = &ss[new_start..];
            }
        }
        // let c = char_iter.next();
    }

    Ok(Expr::List(exprs.into()))
}

#[inline]
fn is_symbol_char(c: char) -> bool {
    c != '(' && c != ')' && !('0' <= c && c <= '9')
}
