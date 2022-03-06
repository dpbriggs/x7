use std::hash::Hash;

use crate::exact_len;
use crate::records::RecordDoc;
use crate::symbols::{Expr, LispResult, SymbolTable};
use anyhow::anyhow;
use im::Vector;
use regex::Regex;

use super::struct_record::StructRecord;

#[derive(Debug, Clone)]
pub(crate) struct RegexRecord {
    re: Regex,
    regex_string: String,
}

impl Default for RegexRecord {
    fn default() -> Self {
        Self {
            re: Regex::new(".*").unwrap(),
            regex_string: ".*".into(),
        }
    }
}

impl PartialEq for RegexRecord {
    fn eq(&self, other: &Self) -> bool {
        self.regex_string == other.regex_string
    }
}

impl Hash for RegexRecord {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.regex_string.hash(state);
    }
}

impl RegexRecord {
    pub(crate) const RECORD_NAME: &'static str = "RegexRecord";

    pub(crate) fn compile_x7(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        symbol_table
            .lookup(&Self::RECORD_NAME.into())?
            .call_fn(exprs, symbol_table)
    }

    fn is_match(&self, s: String) -> bool {
        self.re.is_match(&s)
    }

    fn captures(&self, s: String) -> LispResult<Expr> {
        dbg!(&s);
        dbg!(&self.re);
        self.re.captures_iter(&s).for_each(|cap| {
            dbg!(&cap);
        });
        dbg!(self.re.captures(&s));
        let captures = self
            .re
            .captures_iter(&s)
            .map(|mtch| {
                Expr::Tuple(
                    mtch.iter()
                        .skip(1)
                        .flatten()
                        .map(|m| Expr::string(m.as_str().into()))
                        .collect(),
                )
            })
            .collect();
        dbg!(&captures);
        Ok(Expr::List(captures))
    }

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(RegexRecord::RECORD_NAME)
            .init_fn(&|v: Vec<Expr>| {
                exact_len!(v, 1);
                let re_s = v[0].get_string()?;
                Ok(RegexRecord {
                    re: Regex::new(&re_s)
                        .map_err(|e| anyhow!("Failed to compile the regex: {}", e))?,
                    regex_string: re_s,
                })
            })
            .clone_with(&Clone::clone)
            .display_with(&|regex: &RegexRecord| format!("Regex<{}>", regex.regex_string))
            .add_method("is_match", RegexRecord::is_match)
            .add_method("captures", RegexRecord::captures)
            .build()
    }
}

// impl Record for RegexRecord {
//     fn call_method(
//         &self,
//         sym: &str,
//         args: Vector<Expr>,
//         _symbol_table: &SymbolTable,
//     ) -> LispResult<Expr> {
//         try_call_method!(self, sym, args, is_match, captures)
//     }

//     fn display(&self) -> String {
//         self.debug()
//     }

//     fn debug(&self) -> String {
//         format!("Regex<{}>", self.re)
//     }

//     fn clone(&self) -> super::RecordType {
//         Box::new(Clone::clone(self))
//     }

//     fn methods(&self) -> Vec<String> {
//         RegexRecord::method_doc()
//             .iter()
//             .map(|(l, _)| l.to_string())
//             .collect()
//     }

//     fn type_name(&self) -> String {
//         "Regex".into()
//     }
// }

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
