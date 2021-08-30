use once_cell::sync::Lazy;
use parking_lot::RwLock;
use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    ops::Deref,
};

#[derive(Hash, PartialEq, Eq, Copy, Clone)]
pub struct InternedString(u32, usize);

impl Default for InternedString {
    fn default() -> Self {
        Self(0, 0)
    }
}

impl InternedString {
    #[inline]
    pub(crate) fn new(s: String) -> Self {
        INTERNER.write().intern(s)
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.1
    }

    #[inline]
    fn read(&self) -> String {
        INTERNER.read().fetch(*self)
    }
}

impl PartialEq<str> for InternedString {
    fn eq(&self, other: &str) -> bool {
        self.read() == other
    }
}

impl From<&str> for InternedString {
    fn from(s: &str) -> Self {
        InternedString::new(s.to_string())
    }
}

impl From<String> for InternedString {
    fn from(s: String) -> Self {
        InternedString::new(s)
    }
}

impl Display for InternedString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.read())
    }
}

impl Debug for InternedString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}, {:?}>", self.0, self.read())
    }
}

impl PartialOrd for InternedString {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.read().partial_cmp(&other.read())
    }
}

static INTERNER: Lazy<RwLock<Interner>> = Lazy::new(|| RwLock::new(Interner::new()));

struct Interner {
    id: u32,
    // TODO: Use unsafe hacks here!
    mapping: HashMap<String, InternedString>,
    strings: Vec<String>,
}

impl Interner {
    fn new() -> Self {
        let mut mapping = HashMap::new();
        mapping.insert("".into(), InternedString(0, 0));
        let strings = vec!["".into()];
        Interner {
            id: 0,
            strings,
            mapping,
        }
    }

    #[inline]
    fn get_new_id(&mut self) -> u32 {
        self.id += 1;
        self.id
    }

    fn intern(&mut self, s: String) -> InternedString {
        if let Some(id) = self.mapping.get(s.as_str()) {
            return *id;
        }
        let i = InternedString(self.get_new_id(), s.len());
        self.strings.push(s.clone());
        self.mapping.insert(s, i);
        i
    }

    fn fetch(&self, i: InternedString) -> String {
        self.strings[i.0 as usize].clone()
    }
}
