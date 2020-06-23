use crate::symbols::{DataType, Expr, LispResult, ProgramError};

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
            _ => return Err(ProgramError::FailedToParseInt),
        };
    }
    if periods_seen > 1 {
        return Err(ProgramError::FailedToParseInt);
    }
    let num: f64 = s[..end_pos]
        .parse::<f64>()
        .map_err(|_| ProgramError::FailedToParseInt)?;
    Ok((Expr::new(DataType::Num(num)), end_pos + 1))
}

fn read_str(s: &str) -> LispResult<(Expr, usize)> {
    assert!(s.starts_with('"'));
    s[1..]
        .find('"')
        .map(|end_pos| {
            Ok((
                Expr::new(DataType::String(s[1..=end_pos].into())),
                end_pos + 2,
            ))
        })
        .unwrap_or(Err(ProgramError::FailedToParseString))
}

fn read_word(s: &str) -> LispResult<(Expr, usize)> {
    if s.is_empty() {
        return Err(ProgramError::UnexpectedEOF);
    }
    let end = s.find(' ').unwrap_or_else(|| s.len()); // TODO: Fix strings in words
    Ok((Expr::new(DataType::Symbol(s[..end].into())), end + 1))
}

pub(crate) fn read(s: &str) -> LispResult<Expr> {
    // assert!(s.starts_with('('));
    if s.is_empty() {
        return Ok(Expr::nil());
    }
    let mut exprs = Vec::new();
    let mut ss = s;
    while !ss.is_empty() {
        let first_char = ss.chars().next().unwrap();
        match first_char {
            '0'..='9' => {
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
            ' ' => {
                ss = &ss[1..];
                continue;
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
                    return Err(ProgramError::UnknownSymbol);
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

    Ok(Expr::list(exprs))
}

#[inline]
fn is_symbol_char(c: char) -> bool {
    c != '(' && c != ')' && !('0' <= c && c <= '9')
}
