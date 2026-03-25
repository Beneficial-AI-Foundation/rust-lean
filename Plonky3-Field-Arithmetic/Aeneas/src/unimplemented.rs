/// Dummy `Iterator` placeholder trait
pub trait Iterator {
    /// The type of the elements being iterated over.
    type Item;
}

/// Copied `Sum` trait
pub trait Sum<A = Self>: Sized {
    /// Takes an iterator and generates `Self` from the elements by "summing up"
    /// the items.
    fn sum<I: Iterator<Item = A>>(iter: I) -> Self;
}

/// Copied `Product` trait
pub trait Product<A = Self>: Sized {
    /// Takes an iterator and generates `Self` from the elements by multiplying
    /// the items.
    fn product<I: Iterator<Item = A>>(iter: I) -> Self;
}
