use std::fmt;
use std::net::Ipv4Addr;

/// A smart IPv4 iterator.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
///
/// ```
/// ```
#[derive(Clone, Debug)]
pub struct Ipv4AddrSmartIterator {
    start: u32,
    end: u32,
    curr: u32,
    next: Option<u32>,
    updater: fn(u32) -> u32
}

impl Ipv4AddrSmartIterator {
    /// Returns a `Ipv4AddrSmartIterator`.
    pub fn new (start: Ipv4Addr, end: Ipv4Addr) -> Ipv4AddrSmartIterator {} 
}

impl Iterator for Ipv4AddrSmartIterator {
    type Item = Ipv4Addr;

    fn next (&mut self) -> Option<Self::Item> {}
}

impl fmt::Display for Ipv4AddrSmartIterator {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}-{}", self.start, self.curr, self.end)
    }
}

impl From<(Ipv4Addr, Ipv4Addr)> for Ipv4AddrSmartIterator {
    /// Create an `Ipv4AddrSmartIterator` from a tuple `(Ipv4Addr, Ipv4Addr)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (Ipv4Addr, Ipv4Addr)) -> Ipv4AddrSmartIterator {}
}
