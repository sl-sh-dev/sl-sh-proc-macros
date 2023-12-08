use crate::dialect::Dialect;

pub struct SlSh {}

impl Dialect for SlSh {
    fn dialect(&self) -> Box<dyn Dialect> {
        Box::new(SlSh {})
    }
}
