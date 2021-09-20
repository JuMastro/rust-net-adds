use std::fmt;
use std::net::Ipv6Addr;

/// A smart IPv6 iterator.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
///
/// use net_adds::Ipv6AddrSmartIterator;
///
/// let mut iter = Ipv6AddrSmartIterator::new(Ipv6Addr::from(0), Ipv6Addr::from(1));
///
/// assert_eq!(iter.next(), Some(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0)));
/// assert_eq!(iter.next(), Some(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = Ipv6AddrSmartIterator::new(Ipv6Addr::from(0), Ipv6Addr::from(0));
///
/// assert_eq!(iter.next(), Some(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = Ipv6AddrSmartIterator::new(Ipv6Addr::from(1), Ipv6Addr::from(0));
///
/// assert_eq!(iter.next(), Some(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)));
/// assert_eq!(iter.next(), Some(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0)));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct Ipv6AddrSmartIterator {
    start: u128,
    end: u128,
    curr: u128,
    next: Option<u128>,
    updater: fn(u128) -> u128
}

impl Ipv6AddrSmartIterator {
    /// Returns a `Ipv6AddrSmartIterator`.
    pub fn new (start: Ipv6Addr, end: Ipv6Addr) -> Ipv6AddrSmartIterator {} 
}

impl Iterator for Ipv6AddrSmartIterator {
    type Item = Ipv6Addr;

    fn next (&mut self) -> Option<Self::Item> {}
}

impl fmt::Display for Ipv6AddrSmartIterator {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.start, self.curr, self.end)
    }
}

impl From<(Ipv6Addr, Ipv6Addr)> for Ipv6AddrSmartIterator {
    /// Create an `Ipv6AddrSmartIterator` from a tuple `(Ipv6Addr, Ipv6Addr)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrSmartIterator;
    ///
    /// let mut iter = Ipv6AddrSmartIterator::from((Ipv6Addr::from(0), Ipv6Addr::from(1)));
    ///
    /// assert_eq!(iter.next(), Some(Ipv6Addr::from(0)));
    /// assert_eq!(iter.next(), Some(Ipv6Addr::from(1)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (ips: (Ipv6Addr, Ipv6Addr)) -> Ipv6AddrSmartIterator {}
}
