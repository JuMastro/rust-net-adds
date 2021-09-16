use std::fmt;
use std::net::Ipv6Addr;
use std::str::FromStr;

use crate::errors::NetAddsError;

/// An IPv6 address range.
///
/// See [`crate::IpAddrRange`] for a type encompassing both IPv4 and IPv6 range.
///
/// The size of an `Ipv6AddrRange` struct may vary depending on the target operating
/// system.
///
/// # Textual representation
///
/// `Ipv6AddrRange` provides a [`FromStr`] implementation.
/// The two parts are represented by Ipv6Addr and are separated by '-'.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ipv6AddrRange {
    start: Ipv6Addr,
    end: Ipv6Addr
}

impl Ipv6AddrRange {
    /// Returns an `Ipv6AddrRange`.
    pub fn new (start: Ipv6Addr, end: Ipv6Addr) -> Ipv6AddrRange {
        Ipv6AddrRange { start, end }
    }

    /// Returns the first ip. 
    pub fn start (self) -> Ipv6Addr {
        self.start
    }

    /// Returns the last ip.
    pub fn end (self) -> Ipv6Addr {
        self.end
    }

    /// Returns all ips included in the range.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn all (&self) -> Vec<Ipv6Addr> {}

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn has (&self, ip: Ipv6Addr) -> bool {}
}

impl fmt::Display for Ipv6AddrRange {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", &self.start, &self.end)
    }
}

impl From<(Ipv6Addr, Ipv6Addr)> for Ipv6AddrRange {
    /// Create an `Ipv6AddrRange` from a tuple of two `Ipv6Addr`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (Ipv6Addr, Ipv6Addr)) -> Ipv6AddrRange {}
}

impl FromStr for Ipv6AddrRange {
    type Err = NetAddsError;

    /// Parse a string as `Ipv6AddrRange`.
    ///
    /// If the string representation is not valid return an `NetAddsError::RangeAddrParse(RangeAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}
