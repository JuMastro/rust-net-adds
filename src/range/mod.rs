use std::fmt;
use std::net::IpAddr;
use std::str::FromStr;

use crate::errors::NetAddsError;

mod v4;
pub use v4::*;

mod v6;
pub use v6::*;

/// An IP address range, either IPv4 or IPv6.
///
/// This enum can contain either an [`Ipv4AddrRange`] or an [`Ipv6AddrRange`], see their
/// respective documentation for more details.
///
/// The size of an `IpAddrRange` struct may vary depending on the target operating system.
///
/// # Textual representation
///
/// `IpAddrRange` provides a [`FromStr`] implementation. The two parts are divided by `-`.
/// For IPv4, the two parts must contains an IPv4.
/// For IPv6, the two parts must contains an IPv6.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IpAddrRange {
    V4(Ipv4AddrRange),
    V6(Ipv6AddrRange)
}

impl IpAddrRange {
    /// Returns the first ip.
    pub fn start (self) -> IpAddr {}

    /// Returns the last ip.
    pub fn end (self) -> IpAddr {}

    /// Returns all ips included in the range.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn all (&self) -> Vec<IpAddr> {}

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Panic if IPv4 and IPv6 are mixed.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn has (&self, ip: IpAddr) -> bool {}

    /// Returns true if the range contains IPv4, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn is_ipv4 (&self) -> bool {}

    /// Returns true if the range contains IPv6, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn is_ipv6 (&self) -> bool {}
}

impl fmt::Display for IpAddrRange {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpAddrRange::V4(v4) => write!(f, "V4({})", v4),
            IpAddrRange::V6(v6) => write!(f, "V6({})", v6)
        }
    }
}

impl From<Ipv4AddrRange> for IpAddrRange {
    /// Create an `IpAddrRange::V4` from an `Ipv4AddrRange`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (range: Ipv4AddrRange) -> IpAddrRange {}
}

impl From<Ipv6AddrRange> for IpAddrRange {
    /// Create an `IpAddrRange::V6` from an `Ipv6AddrRange`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (range: Ipv6AddrRange) -> IpAddrRange {}
}

impl FromStr for IpAddrRange {
    type Err = NetAddsError;

    /// Parse a string as `IpAddrRange`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeAddrParseError ();

impl std::error::Error for RangeAddrParseError {}

impl fmt::Display for RangeAddrParseError {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", "invalid IP address range syntax")
    }
}
