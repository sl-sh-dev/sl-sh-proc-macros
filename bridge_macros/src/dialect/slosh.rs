use crate::dialect::Dialect;

pub struct Slosh {}

impl Dialect for Slosh {
    fn dialect(&self) -> Box<dyn Dialect> {
        Box::new(Slosh {})
    }
}
