use std::fmt;
use std::net::Ipv4Addr;
use std::str::FromStr;

use crate::errors::NetAddsError;

/// An IPv4 address range.
///
/// See [`crate::IpAddrRange`] for a type encompassing both IPv4 and IPv6 range.
///
/// The size of an `Ipv4AddrRange` struct may vary depending on the target operating
/// system.
///
/// # Textual representation
///
/// `Ipv4AddrRange` provides a [`FromStr`] implementation.
/// The two parts are represented by Ipv4Addr and are separated by '-'.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ipv4AddrRange {
    start: Ipv4Addr,
    end: Ipv4Addr
}

impl Ipv4AddrRange {
    /// Returns an `Ipv4AddrRange`.
    pub fn new (start: Ipv4Addr, end: Ipv4Addr) -> Ipv4AddrRange {
        Ipv4AddrRange { start, end }
    }

    /// Returns the first ip. 
    pub fn start (self) -> Ipv4Addr {
        self.start
    }

    /// Returns the last ip.
    pub fn end (self) -> Ipv4Addr {
        self.end
    }

    /// Returns all ips included in the range.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn all (&self) -> Vec<Ipv4Addr> {}

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u32 {}

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn has (&self, ip: Ipv4Addr) -> bool {}
}

impl fmt::Display for Ipv4AddrRange {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", &self.start, &self.end)
    }
}

impl From<(Ipv4Addr, Ipv4Addr)> for Ipv4AddrRange {
    /// Create an `Ipv4AddrRange` from a tuple of two `Ipv4Addr`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (ips: (Ipv4Addr, Ipv4Addr)) -> Ipv4AddrRange {}
}

impl FromStr for Ipv4AddrRange {
    type Err = NetAddsError;

    /// Parse a string as `Ipv4AddrRange`.
    ///
    /// If the string representation is not valid return an `NetAddsError::RangeAddrParse(RangeAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}
