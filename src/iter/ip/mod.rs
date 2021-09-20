use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

pub mod v4;
use v4::*;

pub mod v6;
use v6::*;

/// An IP address smart iterator, either IPv4 or IPv6.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
///
/// ```
/// ```
#[derive(Clone, Debug)]
pub enum IpAddrSmartIterator {
    V4(Ipv4AddrSmartIterator),
    V6(Ipv6AddrSmartIterator)
}

impl IpAddrSmartIterator {
    /// Returns true if the iterator is an IPv4 iterator, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn is_ipv4 (&self) -> bool {}

    /// Returns true if the iterator is an IPv6 iterator, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn is_ipv6 (&self) -> bool {}
}

impl Iterator for IpAddrSmartIterator {
    type Item = IpAddr;

    fn next (&mut self) -> Option<Self::Item> {}
}

impl fmt::Display for IpAddrSmartIterator {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpAddrSmartIterator::V4(iter) => write!(f, "V4({})", iter),
            IpAddrSmartIterator::V6(iter) => write!(f, "V6({})", iter)
        }
    }
}

impl From<Ipv4AddrSmartIterator> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator::V4` from an `Ipv4AddrSmartIterator`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (iter: Ipv4AddrSmartIterator) -> IpAddrSmartIterator {}
}

impl From<Ipv6AddrSmartIterator> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator::V6` from an `Ipv6AddrSmartIterator`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (iter: Ipv6AddrSmartIterator) -> IpAddrSmartIterator {}
}

impl From<(IpAddr, IpAddr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` V4 or V6 from a tuple `(IpAddr, IpAddr)`.
    ///
    /// Panic if IPv4 and IPv6 are mixed.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (IpAddr, IpAddr)) -> IpAddrSmartIterator {}
}

impl From<(Ipv4Addr, Ipv4Addr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` from a tuple `(Ipv4Addr, Ipv4Addr)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (Ipv4Addr, Ipv4Addr)) -> IpAddrSmartIterator {}
}


impl From<(Ipv6Addr, Ipv6Addr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` from a tuple `(Ipv6Addr, Ipv6Addr)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (Ipv6Addr, Ipv6Addr)) -> IpAddrSmartIterator {}
}
