use anyhow::{anyhow, bail};
use im::Vector;
use itertools::Itertools;
use parking_lot::RwLock;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::ffi::ForeignData;
use crate::symbols::{Expr, LispResult, SymbolTable};

use crate::records::Record;
use crate::unknown_method;

type ReadFn<T> =
    Box<dyn Fn(&StructRecord<T>, Vector<Expr>, &SymbolTable) -> LispResult<Expr> + Sync + Send>;
type WriteFn<T> =
    Box<dyn Fn(&StructRecord<T>, Vector<Expr>, &SymbolTable) -> LispResult<Expr> + Sync + Send>;
type CloneFn<T> = Arc<dyn Fn(&T) -> T + Sync + Send>;
type InitFn<T> = Arc<dyn Fn(Vector<Expr>) -> LispResult<T> + Sync + Send>;
type DisplayFn<T> = Arc<dyn Fn(&T) -> String + Sync + Send>;

pub(crate) struct StructRecord<T> {
    inner: Arc<RwLock<T>>,
    name: &'static str,
    read_method_map: Arc<HashMap<&'static str, ReadFn<T>>>,
    write_method_map: Arc<HashMap<&'static str, WriteFn<T>>>,
    fields: Arc<Vec<&'static str>>,
    clone_fn: Option<CloneFn<T>>,
    init_fn: Option<InitFn<T>>,
    display_fn: Option<DisplayFn<T>>,
    initialized: bool,
}

impl<T> Clone for StructRecord<T> {
    fn clone(&self) -> Self {
        let inner = match self.clone_fn {
            Some(ref ff) => {
                let guard = self.inner.read();
                Arc::new(RwLock::new((ff)(&guard)))
            }
            None => Arc::clone(&self.inner),
        };
        Self {
            inner,
            name: self.name,
            read_method_map: self.read_method_map.clone(),
            write_method_map: self.write_method_map.clone(),
            fields: self.fields.clone(),
            clone_fn: self.clone_fn.clone(),
            init_fn: self.init_fn.clone(),
            display_fn: self.display_fn.clone(),
            initialized: self.initialized,
        }
    }
}

// trait AsStructRecord {
//     fn call_method(&self, )
// }

// type BizarreF<T> = Fn(T) -> (Fn(T, &[dyn ForeignData], &SymbolTable) -> );

// trait IntoX7RecordMethod<'me, Args, Out> {
//     fn to_x7_read_fn(
//         self,
//     ) -> (
//         usize,
//         Arc<dyn Fn(&'me Self, Vector<Expr>, &'me SymbolTable) -> LispResult<Expr>>,
//     );
// }

// impl<'me, F, Out> IntoX7RecordMethod<'me, ((),), Out> for F
// where
//     F: Fn(&Self) -> Out + 'static,
//     Out: ForeignData,
// {
//     fn to_x7_read_fn(
//         self,
//     ) -> (
//         usize,
//         Arc<dyn Fn(&'me Self, Vector<Expr>, &'me SymbolTable) -> LispResult<Expr>>,
//     ) {
//         let ff = move |s, _args, _sym| (self)(s).to_x7().map_err(|e| anyhow!("{:?}", e));
//         (0, Arc::new(ff))
//     }
// }

// impl<F, Out> IntoX7RecordMethod<((),), Out> for F
// where
//     F: Fn(&Self) -> Out,
//     Out: ForeignData,
// {
//     fn to_x7_fn(self) -> (usize, X7FunctionPtr) {
//         |s: &Self| {

//         }
//         todo!()
//     }
// }

// impl<T> Clone for StructRecord<T> {
//     fn clone(&self) -> Self {
//         Self {
//             inner: Arc::clone(&self.inner),
//             name: self.name,
//             read_method_map: self.read_method_map.clone(),
//             write_method_map: self.write_method_map.clone(),
//             ..Default::default()
//         }
//     }
// }

impl<T: Default + PartialEq + Sync + Send + 'static> StructRecord<T> {
    pub(crate) fn build(self) -> Expr {
        Expr::Record(Box::new(self))
    }
}

impl<T: Default + PartialEq + Sync + Send + 'static> StructRecord<T> {
    fn clone_with_new_inner(&self, new_inner: T) -> Self {
        StructRecord {
            inner: Arc::new(RwLock::new(new_inner)),
            name: self.name,
            read_method_map: self.read_method_map.clone(),
            write_method_map: self.write_method_map.clone(),
            fields: self.fields.clone(),
            clone_fn: self.clone_fn.clone(),
            init_fn: self.init_fn.clone(),
            display_fn: self.display_fn.clone(),
            initialized: self.initialized,
        }
    }
}

impl<T: Default + Sync + Send + 'static + PartialEq> StructRecord<T> {
    pub(crate) fn record_builder(name: &'static str) -> StructRecord<T> {
        StructRecord {
            inner: Arc::new(RwLock::new(T::default())),
            name,
            read_method_map: Default::default(),
            write_method_map: Default::default(),
            fields: Arc::new(Vec::new()),
            clone_fn: None,
            init_fn: None,
            display_fn: None,
            initialized: false,
        }
    }

    pub(crate) fn add_method<Args, Out, F: IntoReadFn<Args, T, Out>>(
        mut self,
        sym: &'static str,
        f: F,
    ) -> Self {
        Arc::get_mut(&mut self.read_method_map)
            .unwrap()
            .insert(sym, f.into_read_fn());
        self
    }

    pub(crate) fn add_method_mut<Args, Out, F: IntoWriteFn<Args, T, Out>>(
        mut self,
        sym: &'static str,
        f: F,
    ) -> Self {
        Arc::get_mut(&mut self.write_method_map)
            .unwrap()
            .insert(sym, f.into_write_fn());
        self
    }

    // pub(crate) fn add_field<Out: ForeignData>(
    //     mut self,
    //     sym: &'static str,
    //     f: &'static (dyn Fn(&T) -> Out + Sync + Send),
    // ) -> Self {
    //     Arc::get_mut(&mut self.fields).unwrap().push(sym);
    //     self.add_method_zero(sym, f)
    // }

    pub(crate) fn clone_with(mut self, f: &'static (dyn Fn(&T) -> T + Sync + Send)) -> Self {
        self.clone_fn = Some(Arc::new(f));
        self
    }

    pub(crate) fn display_with(mut self, f: &'static (dyn Fn(&T) -> String + Sync + Send)) -> Self {
        self.display_fn = Some(Arc::new(f));
        self
    }

    pub(crate) fn init_fn<I: ForeignData + std::fmt::Debug>(
        mut self,
        f: &'static (dyn Fn(Vec<I>) -> LispResult<T> + Sync + Send),
    ) -> Self {
        self.init_fn = Some(Arc::new(move |v: Vector<Expr>| {
            let mut my_v = Vec::with_capacity(v.len());
            for i in v {
                let converted = crate::convert_arg!(I, &i);
                my_v.push(converted)
            }
            (f)(my_v)
        }));
        self
    }
}

impl<T: 'static + Send + Sync + Default + PartialEq> Record for StructRecord<T> {
    fn call_method(
        &self,
        sym: &str,
        args: Vector<Expr>,
        symbol_table: &SymbolTable,
    ) -> LispResult<Expr> {
        if self.initialized {
            if let Some(ff) = self.read_method_map.get(sym) {
                return (ff)(self, args, symbol_table);
            }
            if let Some(ff) = self.write_method_map.get(sym) {
                return (ff)(self, args, symbol_table);
            }
            unknown_method!(self, sym)
        } else {
            bail!(
                "Method {} called on uninitialized record {} with args [ {} ]",
                sym,
                self.display(),
                args.iter().join(" ")
            )
        }
    }

    fn display(&self) -> String {
        self.debug()
    }

    fn debug(&self) -> String {
        if self.initialized {
            match self.display_fn {
                Some(ref ff) => {
                    let guard = self.inner.read();
                    (ff)(&guard)
                }
                None => format!(
                    "Record<{} field=[ {} ]>",
                    self.name,
                    self.fields.iter().join(" ")
                ),
            }
        } else {
            format!("Record<{}, uninitialized>", self.name)
        }
    }

    fn clone(&self) -> super::RecordType {
        Box::new(Clone::clone(self))
    }

    fn methods(&self) -> Vec<String> {
        self.read_method_map
            .keys()
            .chain(self.write_method_map.keys())
            .map(|s| s.to_string())
            .collect()
    }

    fn type_name(&self) -> String {
        self.name.into()
    }

    fn id(&self) -> u64 {
        0
    }

    fn get_type_str(&self) -> String {
        self.type_name()
    }

    fn call_as_fn(&self, args: Vector<Expr>, _symbol_table: &SymbolTable) -> LispResult<Expr> {
        match self.init_fn {
            Some(ref ff) => {
                let new_inner = (ff)(args).map_err(|e| anyhow!("{:?}", e))?;
                let mut new_me = Clone::clone(self);
                new_me.inner = Arc::new(RwLock::new(new_inner));
                new_me.initialized = true;
                crate::record!(new_me)
            }
            None => crate::record!(StructRecord {
                initialized: true,
                ..Clone::clone(self)
            }),
        }
    }

    fn is_equal(&self, other: &dyn Record) -> bool {
        match other.downcast_ref::<Self>() {
            Some(sr_other) => *self.inner.read() == *sr_other.inner.read(),
            None => false,
        }
    }
}

// Massive set of trait impls
// TODO: Use a macro for this

pub(crate) trait IntoReadFn<Args, T, Out> {
    fn into_read_fn(self) -> ReadFn<T>;
}

pub(crate) trait IntoWriteFn<Args, T, Out> {
    fn into_write_fn(self) -> WriteFn<T>;
}

// Struct to prevent trait impl issues for Self: ForeignData
pub(crate) struct InnerBlocker<T>(PhantomData<T>);

// IntoReadFn: Zero args

impl<F, T, Out> IntoReadFn<(), T, Out> for F
where
    F: Fn(&T) -> Out + Sync + Send + 'static,
    Out: ForeignData,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 0);
            let s = sr.inner.read();
            (self)(&s).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

impl<F, T> IntoReadFn<(), T, InnerBlocker<T>> for F
where
    F: Fn(&T) -> T + Sync + Send + 'static,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 0);
            let my_inner = sr.inner.read();
            let new_inner = (self)(&my_inner);
            crate::record!(sr.clone_with_new_inner(new_inner))
        };
        Box::new(ff)
    }
}

// IntoReadFn: One arg

impl<F, T, A, Out> IntoReadFn<(A,), T, Out> for F
where
    F: Fn(&T, A) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let a = crate::convert_arg!(A, &args[0]);
            let s = sr.inner.read();
            (self)(&s, a).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

impl<F, T, A> IntoReadFn<(A,), T, InnerBlocker<LispResult<Self>>> for F
where
    F: Fn(&T, A) -> LispResult<T> + Sync + Send + 'static,
    A: ForeignData,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let a = crate::convert_arg!(A, &args[0]);
            let s = sr.inner.read();
            let new_inner = (self)(&s, a)?;
            crate::record!(sr.clone_with_new_inner(new_inner))
        };
        Box::new(ff)
    }
}

// IntoReadFn: Two args

impl<F, T, A, Out> IntoReadFn<(A,), T, InnerBlocker<(T, (Out,))>> for F
where
    F: Fn(&T, &T) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let other = args[0].get_record()?;
            match other.downcast_ref::<StructRecord<T>>() {
                Some(other_rec) => {
                    // TODO: Deadlock if same?
                    let my_inner = sr.inner.read();
                    let other_inner = other_rec.inner.read();
                    (self)(&my_inner, &other_inner)
                        .to_x7()
                        .map_err(|e| anyhow!("{:?}", e))
                }
                None => crate::bad_types!(sr as &dyn Record, other), // TODO: Handle this
            }
        };
        Box::new(ff)
    }
}

impl<F, T> IntoReadFn<(T,), T, InnerBlocker<(T, T)>> for F
where
    F: Fn(&T, &T) -> T + Sync + Send + 'static,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let other = args[0].get_record()?;
            match other.downcast_ref::<StructRecord<T>>() {
                Some(other_rec) => {
                    // TODO: Deadlock if same?
                    let my_inner = sr.inner.read();
                    let other_inner = other_rec.inner.read();
                    let new_inner = (self)(&my_inner, &other_inner);
                    crate::record!(sr.clone_with_new_inner(new_inner))
                }
                None => crate::bad_types!(sr as &dyn Record, other), // TODO: Handle this
            }
        };
        Box::new(ff)
    }
}

// IntoReadFn: Three Args

impl<F, T, A, B, Out> IntoReadFn<(A, B), T, Out> for F
where
    F: Fn(&T, A, B) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
    B: ForeignData,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 2);
            let a = crate::convert_arg!(A, &args[0]);
            let b = crate::convert_arg!(B, &args[1]);
            let s = sr.inner.read();
            (self)(&s, a, b).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

impl<F, T, A, B, C, Out> IntoReadFn<(A, B, C), T, Out> for F
where
    F: Fn(&T, A, B, C) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
    B: ForeignData,
    C: ForeignData,
{
    fn into_read_fn(self) -> ReadFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 3);
            let a = crate::convert_arg!(A, &args[0]);
            let b = crate::convert_arg!(B, &args[1]);
            let c = crate::convert_arg!(C, &args[2]);
            let s = sr.inner.read();
            (self)(&s, a, b, c).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

// IntoWriteFn

// IntoWriteFn: Zero args

impl<F, T, Out> IntoWriteFn<(), T, Out> for F
where
    F: Fn(&mut T) -> Out + Sync + Send + 'static,
    Out: ForeignData,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 0);
            let mut s = sr.inner.write();
            (self)(&mut s).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

impl<F, T> IntoWriteFn<(), T, InnerBlocker<T>> for F
where
    F: Fn(&mut T) -> T + Sync + Send + 'static,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 0);
            let mut my_inner = sr.inner.write();
            let new_inner = (self)(&mut my_inner);
            crate::record!(sr.clone_with_new_inner(new_inner))
        };
        Box::new(ff)
    }
}

// IntoWriteFn: One arg

impl<F, T, A, Out> IntoWriteFn<(A,), T, Out> for F
where
    F: Fn(&mut T, A) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let a = crate::convert_arg!(A, &args[0]);
            let mut s = sr.inner.write();
            (self)(&mut s, a).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

// IntoWriteFn: Two args

impl<F, T, Out> IntoWriteFn<((), ((),)), T, InnerBlocker<((), (Out,))>> for F
where
    F: Fn(&mut T, &T) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let other = args[0].get_record()?;
            match other.downcast_ref::<StructRecord<T>>() {
                Some(other_rec) => {
                    // TODO: Deadlock if same?
                    let mut my_inner = sr.inner.write();
                    let other_inner = other_rec.inner.read();
                    (self)(&mut my_inner, &other_inner)
                        .to_x7()
                        .map_err(|e| anyhow!("{:?}", e))
                }
                None => crate::bad_types!(sr as &dyn Record, other), // TODO: Handle this
            }
        };
        Box::new(ff)
    }
}

impl<F, T> IntoWriteFn<(T,), T, InnerBlocker<(T, T)>> for F
where
    F: Fn(&mut T, &T) -> T + Sync + Send + 'static,
    T: Default + PartialEq + Sync + Send + 'static,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 1);
            let other = args[0].get_record()?;
            match other.downcast_ref::<StructRecord<T>>() {
                Some(other_rec) => {
                    // TODO: Deadlock if same?
                    let mut my_inner = sr.inner.write();
                    let other_inner = other_rec.inner.read();
                    let new_inner = (self)(&mut my_inner, &other_inner);
                    crate::record!(sr.clone_with_new_inner(new_inner))
                }
                None => crate::bad_types!(sr as &dyn Record, other), // TODO: Handle this
            }
        };
        Box::new(ff)
    }
}

// IntoWriteFn: Three Args

impl<F, T, A, B, Out> IntoWriteFn<(A, B), T, Out> for F
where
    F: Fn(&mut T, A, B) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
    B: ForeignData,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 2);
            let a = crate::convert_arg!(A, &args[0]);
            let b = crate::convert_arg!(B, &args[1]);
            let mut s = sr.inner.write();
            (self)(&mut s, a, b).to_x7().map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}

impl<F, T, A, B, C, Out> IntoWriteFn<(A, B, C), T, Out> for F
where
    F: Fn(&mut T, A, B, C) -> Out + Sync + Send + 'static,
    Out: ForeignData,
    A: ForeignData,
    B: ForeignData,
    C: ForeignData,
{
    fn into_write_fn(self) -> WriteFn<T> {
        let ff = move |sr: &StructRecord<T>, args: Vector<Expr>, _sym: &SymbolTable| {
            crate::exact_len!(args, 3);
            let a = crate::convert_arg!(A, &args[0]);
            let b = crate::convert_arg!(B, &args[1]);
            let c = crate::convert_arg!(C, &args[2]);
            let mut s = sr.inner.write();
            (self)(&mut s, a, b, c)
                .to_x7()
                .map_err(|e| anyhow!("{:?}", e))
        };
        Box::new(ff)
    }
}
