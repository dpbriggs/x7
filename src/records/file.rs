use crate::exact_len;
use crate::records::{Record, RecordDoc, RecordType};
use crate::symbols::{Expr, LispResult, SymbolTable};
use crate::{num, record, unknown_method};
use anyhow::anyhow;
use im::Vector;
use parking_lot::Mutex;
use std::fs;
use std::fs::OpenOptions;
use std::io::{Read, Seek, Write};
use std::sync::Arc;

macro_rules! rewind_file {
    ($guard:expr) => {
        $guard
            .seek(std::io::SeekFrom::Start(0))
            .map_err(|e| anyhow!("Failed to seek to position 0, {}", e))?;
    };
}

macro_rules! write_file {
    ($guard:expr, $content:expr) => {
        $guard
            .write_all($content.as_bytes())
            .map_err(|e| anyhow!("Failed to write to file, {}", e))?;
    };
}
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
        let f = OpenOptions::new()
            .write(true)
            .create(true)
            .read(true)
            .open(path.clone())
            .map_err(|e| anyhow!("Error: Could not open file {}", e))?;
        record!(FileRecord::new(f, path))
    }

    fn read_to_string(&self) -> LispResult<Expr> {
        let mut buf = String::new();
        let mut guard = self.file.lock();
        guard
            .read_to_string(&mut buf)
            .map_err(|e| anyhow!("Failed to read to string {}", e))?;
        rewind_file!(guard);
        Ok(Expr::String(buf))
    }

    fn write_to_file(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let content = args[0].get_string()?;
        let content_len = num!(content.len());
        let mut guard = self.file.lock();
        guard
            .set_len(0)
            .map_err(|e| anyhow!("Failed to shrink file to 0, {}", e))?;
        write_file!(guard, content);
        rewind_file!(guard);
        guard
            .flush()
            .map_err(|e| anyhow!("Failed to flush file {}", e))?;
        Ok(content_len)
    }

    fn append(&self, content: &str) -> LispResult<Expr> {
        let content_len = num!(content.len());
        let mut guard = self.file.lock();

        guard
            .seek(std::io::SeekFrom::End(0))
            .map_err(|e| anyhow!("Could not seek to end of file! {}", e))?;
        write_file!(guard, content);
        rewind_file!(guard);
        Ok(content_len)
    }

    fn append_to_file(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let content = args[0].get_string()?;
        self.append(&content)
    }

    fn append_line(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let content = args[0].get_string()?;
        self.append(&format!("{}\n", content))
    }
}

impl Record for FileRecord {
    fn call_method(&self, sym: &str, args: Vector<Expr>) -> LispResult<Expr> {
        match sym {
            "read_to_string" => self.read_to_string(),
            "write_to_file" => self.write_to_file(args),
            "append_to_file" => self.append_to_file(args),
            "append_line" => self.append_line(args),
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
        &[
            "read_to_string",
            "write_to_file",
            "append_to_file",
            "append_line",
        ]
    }
}

impl RecordDoc for FileRecord {
    fn name() -> &'static str {
        "FileRecord"
    }

    fn type_doc() -> &'static str {
        "Manipulate files in x7.
Example:
(def my-file (fs::open \"my_file.txt\"))

;; Write to the file
(.write_to_file my-file \"Hello World\")

;; Read from the file
(.read_to_string my-file)
"
    }

    fn method_doc() -> Vec<(&'static str, &'static str)> {
        vec![
            (
                "read_to_string",
                "Read a files as a string.
Example:
(def my-file (fs::open \"my_file.txt\"))
(.read_to_string my-file) ; file contents
",
            ),
            (
                "write_to_file",
                "Overwrite the file's content with the given string.
Example:
(def new-file (fs::open \"new_file.txt\"))
(.write_to_file \"Hello world!\")
",
            ),
            (
                "append_to_file",
                "Append to a file without a newline.
Example:
(def new-file (fs::open \"new_file.txt\"))
(.append_to_file \"Hello world!\") ; file contains '...old-contents...Hello world!'

",
            ),
            (
                "append_line",
                "Append a string to a file with a newline.
Example:
(def new-file (fs::open \"new_file.txt\"))
(.append_line \"Hello world!\") ; file contains '...old-contents...Hello world!\n'
",
            ),
        ]
    }
}
