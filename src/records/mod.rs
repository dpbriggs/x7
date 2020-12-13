pub mod file;
pub mod record;
pub mod regex;

pub(crate) use self::file::FileRecord;
pub(crate) use self::record::{Record, RecordDoc, RecordType};
pub(crate) use self::regex::RegexRecord;
