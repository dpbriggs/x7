use crate::exact_len;
use crate::records::{Record, RecordDoc, RecordType};
use crate::symbols::{Expr, LispResult, SymbolTable};
use crate::{num, record, try_call_method, unknown_method};
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
        // TODO: Allow access to OpenOptions in x7.
        // Open the file with liberal permissions.
        let f = OpenOptions::new()
            .write(true)
            .create(true)
            .read(true)
            .open(path.clone())
            .map_err(|e| anyhow!("Could not open file \"{}\" because {}", &path, e))?;
        // Make the path pretty.
        let abs_path = fs::canonicalize(path)
            .map_err(|e| anyhow!("Could not canonicalize path! {}", e))?
            .to_str()
            .ok_or_else(|| anyhow!("Could not represent path as UTF-8 string"))?
            .into();
        record!(FileRecord::new(f, abs_path))
    }

    fn read_all(&self) -> LispResult<String> {
        let mut buf = String::new();
        let mut guard = self.file.lock();
        guard
            .read_to_string(&mut buf)
            .map_err(|e| anyhow!("Failed to read to string {}", e))?;
        rewind_file!(guard);
        Ok(buf)
    }

    fn read_to_string(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 0);
        self.read_all().map(Expr::String)
    }

    fn try_shrink(&self, file: &mut std::fs::File) -> LispResult<()> {
        let metadata = file
            .metadata()
            .map_err(|e| anyhow!("Failed to get metadata for file, {}", e))?;
        if metadata.len() == 0 {
            Ok(())
        } else {
            file.set_len(0)
                .map_err(|e| anyhow!("Failed to shrink file to 0, {}", e))
        }
    }

    fn write(&self, args: Vector<Expr>) -> LispResult<Expr> {
        exact_len!(args, 1);
        let content = args[0].get_string()?;
        let content_len = num!(content.len());
        let mut guard = self.file.lock();
        // Set the length to 0.
        self.try_shrink(&mut guard)?;
        // Write the string
        write_file!(guard, content);
        // Set the cursor to pos 0
        rewind_file!(guard);
        // Flush the changes
        guard
            .flush()
            .map_err(|e| anyhow!("Failed to flush file {}", e))?;
        Ok(content_len)
    }

    fn read_lines(&self, _args: Vector<Expr>) -> LispResult<Expr> {
        let contents = self.read_all()?;
        let split: im::Vector<Expr> = contents
            .split('\n')
            .map(|s| Expr::String(s.into()))
            .collect();
        Ok(Expr::List(split))
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
        self.append(&format!("\n{}", content))
    }
}

impl Record for FileRecord {
    fn call_method(
        &self,
        sym: &str,
        args: Vector<Expr>,
        _symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        try_call_method!(
            self,
            sym,
            args,
            read_to_string,
            read_lines,
            write,
            append_to_file,
            append_line
        )
    }

    fn type_name(&self) -> String {
        "FileRecord".into()
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

    fn methods(&self) -> Vec<String> {
        FileRecord::method_doc()
            .iter()
            .map(|(l, _)| l.to_string())
            .collect()
    }

    fn id(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        self.path.hash(&mut h);
        h.finish()
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
(.write my-file \"Hello World\")

;; Read from the file
(.read_to_string my-file)
"
    }

    fn method_doc() -> &'static [(&'static str, &'static str)] {
        &[
            (
                "read_to_string",
                "Read a files as a string.
Example:
(def my-file (fs::open \"my_file.txt\"))
(.read_to_string my-file) ; file contents
",
            ),
            (
                "read_lines",
                "Get all lines of a file as a list.
Example:
(def my-file (fs::open \"my_file.txt\"))
(.read_lines my-file) ; '(\"first_line\" \"second_line\")
",
            ),
            (
                "write",
                "Overwrite the file's content with the given string.
Example:
(def new-file (fs::open \"new_file.txt\"))
(.write \"Hello world!\")
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
