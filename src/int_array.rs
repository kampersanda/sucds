//!
//!
//!

///
pub trait IntArray {
    ///
    fn get(&self, i: usize) -> usize;

    ///
    fn len(&self) -> usize;

    ///
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl IntArray for Vec<usize> {
    fn get(&self, i: usize) -> usize {
        (*self)[i]
    }

    fn len(&self) -> usize {
        self.len()
    }
}

impl IntArray for [usize] {
    fn get(&self, i: usize) -> usize {
        (*self)[i]
    }

    fn len(&self) -> usize {
        self.len()
    }
}
