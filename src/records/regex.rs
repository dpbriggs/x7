use std::hash::Hash;

use crate::records::{Record, RecordDoc};
use crate::symbols::{Expr, LispResult, SymbolTable};
use crate::{exact_len, record, try_call_method, unknown_method};
use anyhow::anyhow;
use im::Vector;
use regex::Regex;

#[derive(Debug, Clone)]
pub(crate) struct RegexRecord {
    re: Regex,
    regex_string: String,
}

impl Hash for RegexRecord {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.regex_string.hash(state);
    }
}

impl RegexRecord {
    pub(crate) fn compile_x7(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        let re_s = exprs[0].get_string()?;
        let re = RegexRecord {
            re: Regex::new(&re_s).map_err(|e| anyhow!("Failed to compile the regex: {}", e))?,
            regex_string: re_s,
        };
        record!(re)
    }

    fn is_match(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let s = args[0].get_string()?;
        Ok(Expr::Bool(self.re.is_match(&s)))
    }

    fn captures(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let s = args[0].get_string()?;
        let captures = self
            .re
            .captures_iter(&s)
            .map(|mtch| {
                Expr::Tuple(
                    mtch.iter()
                        .skip(1)
                        .flatten()
                        .map(|m| Expr::String(m.as_str().into()))
                        .collect(),
                )
            })
            .collect();
        Ok(Expr::List(captures))
    }
}

impl Record for RegexRecord {
    fn call_method(&self, sym: &str, args: Vector<Expr>) -> LispResult<Expr> {
        try_call_method!(self, sym, args, is_match, captures)
    }

    fn display(&self) -> String {
        self.debug()
    }

    fn debug(&self) -> String {
        format!("Regex<{}>", self.re)
    }

    fn clone(&self) -> super::RecordType {
        Box::new(Clone::clone(self))
    }

    fn methods(&self) -> Vec<&'static str> {
        RegexRecord::method_doc().iter().map(|(l, _)| *l).collect()
    }

    fn type_name(&self) -> &'static str {
        "Regex"
    }
}

impl RecordDoc for RegexRecord {
    fn name() -> &'static str {
        "Regex"
    }

    fn type_doc() -> &'static str {
        "Regular Expressions - regular search patterns.

This is backed by the excellent regex crate: https://github.com/rust-lang/regex

Example:

;; Compile a regex
(def a (re::compile \"(abc)+\"))

;; Test if a string matches

(.is_match a \"abcabc\") ;; true
(.is_match a \"ab\") ;; false
"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[
            (
                "is_match",
                "Returns true if a string matches the regex.

Example:
(def re (re::compile \"abc\"))
(assert-eq true (.is_match re \"abc\") \"Did not match!\")",
            ),
            (
                "captures",
                "Returns a list of lists of all captures in the input.
;; Example
(def lines \"15-16 f: ffffffffffffffhf
             6-8 b: bbbnvbbb
             6-10 z: zhzzzzfzzzzzzzzzpzz
             9-13 s: dmssskssqsssssf\")
(def re (re::compile \"(\\d+)-(\\d+) (.): (.*)\"))
(.captures re lines)
;; Outputs:
((tuple \"15\" \"16\" \"f\" \"ffffffffffffffhf\")
 (tuple \"6\" \"8\" \"b\" \"bbbnvbbb\")
 (tuple \"6\" \"10\" \"z\" \"zhzzzzfzzzzzzzzzpzz\")
 (tuple \"9\" \"13\" \"s\" \"dmssskssqsssssf\"))
",
            ),
        ]
    }
}
