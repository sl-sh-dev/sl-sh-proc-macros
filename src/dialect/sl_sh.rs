use crate::dialect::{Dialect, DialectWrapper, GetItemFn};
use std::marker::PhantomData;

pub struct SlSh<T: ?Sized> {
    phantom: Option<PhantomData<T>>,
}

impl<T: ?Sized> SlSh<T> {
    pub fn new() -> Self {
        Self { phantom: None }
    }
}

impl<T> Dialect for SlSh<T>
where
    T: Dialect,
{
    type OriginalItemFn = dyn GetItemFn;

    fn dialect(&self) -> Box<dyn Dialect<OriginalItemFn = dyn GetItemFn>> {
        Box::new(SlSh { phantom: None })
    }
}
