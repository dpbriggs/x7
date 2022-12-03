use crate::records::RecordDoc;
use crate::symbols::{Expr, LispResult, SymbolTable};
use anyhow::anyhow;
use im::Vector;
use std::fs::OpenOptions;
use std::fs::{self, File};
use std::io::{Read, Seek, Write};

use super::struct_record::StructRecord;

#[derive(Debug)]
pub(crate) struct FileRecord {
    path: String,
    file: Option<std::fs::File>,
}

// TODO: Remove this
impl Default for FileRecord {
    fn default() -> Self {
        Self {
            path: "<no path>".to_string(),
            file: None,
        }
    }
}

impl PartialEq for FileRecord {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
    }
}

impl FileRecord {
    pub(crate) const RECORD_NAME: &'static str = "FileRecord";

    pub(crate) fn from_x7(exprs: Vector<Expr>, symbol_table: &SymbolTable) -> LispResult<Expr> {
        symbol_table
            .lookup(&Self::RECORD_NAME.into())?
            .call_fn(exprs, symbol_table)
    }

    fn new(f: fs::File, path: String) -> FileRecord {
        FileRecord {
            file: Some(f),
            path,
        }
    }

    pub(crate) fn open_file(path: String) -> LispResult<Self> {
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
        Ok(FileRecord::new(f, abs_path))
    }

    fn rewind_file(&mut self) -> LispResult<()> {
        self.get_file()?
            .seek(std::io::SeekFrom::Start(0))
            .map(|_| ())
            .map_err(|e| anyhow!("{:?}", e))
    }

    fn read_all(&mut self) -> LispResult<String> {
        let mut buf = String::new();
        self.get_file()?
            .read_to_string(&mut buf)
            .map_err(|e| anyhow!("Failed to read to string {}", e))?;
        self.rewind_file()?;
        Ok(buf)
    }

    fn read_to_string(&mut self) -> LispResult<Expr> {
        self.read_all().map(Expr::string)
    }

    fn len(&mut self) -> LispResult<usize> {
        self.get_file()?
            .metadata()
            .map(|m| m.len() as usize)
            .map_err(|e| anyhow!("Failed to get metadata for file, {}", e))
    }

    fn try_shrink(&mut self) -> LispResult<()> {
        if self.len()? == 0 {
            Ok(())
        } else {
            self.get_file()?
                .set_len(0)
                .map_err(|e| anyhow!("Failed to shrink file to 0, {}", e))
        }
    }

    fn get_file(&mut self) -> LispResult<&mut File> {
        self.file
            .as_mut()
            .ok_or_else(|| anyhow!("Somehow called methods on uninit file"))
    }

    fn write_to_file(&mut self, content: String) -> LispResult<()> {
        self.get_file()?
            .write_all(content.as_bytes())
            .map_err(|e| anyhow!("{:?}", e))
            .map(|_| ())
    }

    fn write(&mut self, content: String) -> LispResult<Expr> {
        let content_len = Expr::num(content.len());
        // Set the length to 0.
        self.try_shrink()?;
        // Write the string
        self.write_to_file(content)?;
        // Set the cursor to pos 0
        self.rewind_file()?;
        // Flush the changes
        self.get_file()?
            .flush()
            .map_err(|e| anyhow!("Failed to flush file {}", e))?;
        Ok(content_len)
    }

    fn read_lines(&mut self) -> LispResult<Expr> {
        let contents = self.read_all()?;
        let split: im::Vector<Expr> = contents
            .split('\n')
            .map(|s| Expr::string(s.into()))
            .collect();
        Ok(Expr::Tuple(split))
    }

    fn append(&mut self, content: String) -> LispResult<Expr> {
        let content_len = Expr::num(content.len());
        self.get_file()?
            .seek(std::io::SeekFrom::End(0))
            .map_err(|e| anyhow!("Could not seek to end of file! {}", e))?;
        self.write_to_file(content)?;
        self.rewind_file()?;
        Ok(content_len)
    }

    fn append_to_file(&mut self, content: String) -> LispResult<Expr> {
        self.append(content)
    }

    fn append_line(&mut self, content: String) -> LispResult<Expr> {
        self.append(format!("\n{}", content))
    }

    pub(crate) fn make() -> Expr {
        StructRecord::record_builder(FileRecord::RECORD_NAME)
            .display_with(&|me: &Self| format!("File<{}>", me.path))
            .init_fn(&|v: Vec<Expr>, _| FileRecord::open_file(v[0].to_string()))
            .add_method_mut("read_to_string", FileRecord::read_to_string)
            .add_method_mut("read_lines", FileRecord::read_lines)
            .add_method_mut("write", FileRecord::write)
            .add_method_mut("append_to_file", FileRecord::append_to_file)
            .add_method_mut("append_line", FileRecord::append_line)
            .add_method_mut("len", FileRecord::len)
            .build()
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
