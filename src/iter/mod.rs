mod ip;
pub use ip::*;
pub use ip::v4::*;
pub use ip::v6::*;

mod port;
pub use port::*;

mod socket;
pub use socket::*;

/// Conversion into a smart `Iterator`.
///
/// A smart iterator is an iterator that does not store all the items in memory. It's usefull for long series.
///
/// By implementing `IntoSmartIterator` for a type, you define how it will be converted to an smart iterator.
///
/// This is common for types which describe a followed collection of some kind.
pub trait IntoSmartIterator<T> {
    /// The type of the elements being iterated over.
    type Item;

    /// Which kind of iterator are we turning this into?
    type IntoSmartIter: Iterator;

    /// Transform the ouput.
    fn transform (self) -> T;

    /// Creates an iterator from the current struct.
    fn into_smart_iter (self) -> Self::IntoSmartIter;
}
