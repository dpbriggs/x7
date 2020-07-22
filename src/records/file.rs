use crate::exact_len;
use crate::records::{Record, RecordType};
use crate::symbols::{Expr, LispResult, SymbolTable};
use anyhow::anyhow;
use im::Vector;
use parking_lot::Mutex;
use std::fs;
use std::sync::Arc;

use crate::{record, unknown_method};

#[derive(Clone, Debug)]
pub(crate) struct FileRecord {
    path: String,
    file: Arc<Mutex<std::fs::File>>,
}

impl FileRecord {
    pub(crate) fn from_x7(exprs: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
        exact_len!(exprs, 1);
        let path = exprs[0].get_string()?;
        FileRecord::open_file(path)
    }
    fn new(f: fs::File, path: String) -> FileRecord {
        FileRecord {
            file: Arc::new(Mutex::new(f)),
            path,
        }
    }
    pub(crate) fn open_file(path: String) -> LispResult<Expr> {
        let f = fs::File::open(path.clone()).map_err(|e| anyhow!("{}", e))?;
        record!(FileRecord::new(f, path))
    }

    fn read_to_string(&self) -> LispResult<Expr> {
        use std::io::{Read, Seek};
        let mut buf = String::new();
        let mut guard = self.file.lock();
        guard
            .read_to_string(&mut buf)
            .map_err(|e| anyhow!("Failed to read to string {}", e))?;
        guard
            .seek(std::io::SeekFrom::Start(0))
            .map_err(|e| anyhow!("Failed to seek to position 0, {}", e))?;
        Ok(Expr::String(buf))
    }
}

impl Record for FileRecord {
    fn call_method(&self, sym: &str, _args: Vector<Expr>) -> LispResult<Expr> {
        match sym {
            "read_to_string" => self.read_to_string(),
            _ => unknown_method!(self, sym),
        }
    }

    fn display(&self) -> String {
        format!("File<{}>", self.path)
    }

    fn debug(&self) -> String {
        self.display()
    }

    fn clone(&self) -> RecordType {
        Box::new(Clone::clone(self))
    }

    fn methods(&self) -> &'static [&'static str] {
        &["read_to_string"]
    }
}
