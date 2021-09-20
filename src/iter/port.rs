use std::fmt;

/// An smart port iterator.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
/// 
/// ```
/// use net_adds::PortSmartIterator;
///
/// let mut iter = PortSmartIterator::new(0, 2);
///
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = PortSmartIterator::new(0, 0);
///
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), None);
/// 
/// let mut iter = PortSmartIterator::new(1, 0);
///
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct PortSmartIterator {
    start: u16,
    end: u16,
    curr: u16,
    next: Option<u16>,
    updater: fn(u16) -> u16
}

impl PortSmartIterator {
    /// Returns a `PortSmartIterator`.
    pub fn new (start: u16, end: u16) -> PortSmartIterator {}
}

impl Iterator for PortSmartIterator {
    type Item = u16;

    fn next (&mut self) -> Option<Self::Item> {}
}

impl fmt::Display for PortSmartIterator {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.start, self.curr, self.end)
    }
}
