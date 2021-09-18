use std::fmt;
use std::net::IpAddr;
use std::str::FromStr;

use crate::errors::NetAddsError;

mod v4;
pub use v4::*;

mod v6;
pub use v6::*;

/// An IP address network, either IPv4 or IPv6.
///
/// This enum can contain either an [`Ipv4AddrNetwork`] or an [`Ipv6AddrNetwork`], see their
/// respective documentation for more details.
///
/// The size of an `IpAddrNetwork` struct may vary depending on the target operating system.
///
/// # Textual representation
///
/// `IpAddrNetwork` provides a [`FromStr`] implementation. The two parts are divided by `/`.
///
/// For IPv4, the first part must contain an IPv4. The second part can either contain an IPv4
/// or an u8 between 0 and 32 which is valid as a netmask prefix.
///
/// For IPv6, the first part must contain an IPv6. The second part can either contain an IPv6
/// or an u8 between 0 and 128 which is valid as a netmask prefix.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IpAddrNetwork {
    V4(Ipv4AddrNetwork),
    V6(Ipv6AddrNetwork)
}

impl IpAddrNetwork {
    /// Returns the ip addr.
    pub fn ip (self) -> IpAddr {}

    /// Returns the netmask prefix.
    pub fn prefix (self) -> u8 {}

    /// Returns the netmask addr.
    pub fn netmask (self) -> IpAddr {}

    /// Returns the network addr.
    pub fn network (self) -> IpAddr {}

    /// Returns the broadcast addr.
    pub fn broadcast (self) -> IpAddr {}

    /// Returns all ip of the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn all (self) -> Vec<IpAddr> {}

    /// Returns all hosts (exclude network & broadcast).
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn hosts (self) -> Vec<IpAddr> {}

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the network, else returns false.
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

    /// Returns true if the network contains IPv6, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// ```
    pub fn is_ipv6 (&self) -> bool {}
}

impl fmt::Display for IpAddrNetwork {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpAddrNetwork::V4(v4) => write!(f, "V4({})", v4),
            IpAddrNetwork::V6(v6) => write!(f, "V6({})", v6)
        }
    }
}

impl From<Ipv4AddrNetwork> for IpAddrNetwork {
    /// Create an `IpAddrNetwork::V4` from an `Ipv4AddrNetwork`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (network: Ipv4AddrNetwork) -> IpAddrNetwork {}
}

impl From<Ipv6AddrNetwork> for IpAddrNetwork {
    /// Create an `IpAddrNetwork::V6` from an `Ipv6AddrNetwork`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from (network: Ipv6AddrNetwork) -> IpAddrNetwork {}
}

impl FromStr for IpAddrNetwork {
    type Err = NetAddsError;

    /// Parse a string as `IpAddrNetwork`.
    /// 
    /// If the string representation is not valid return an `NetAddsErrorAddrParse(NetworkAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NetworkAddrParseError ();

impl std::error::Error for NetworkAddrParseError {}

impl fmt::Display for NetworkAddrParseError {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", "invalid IP address network syntax")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidNetmaskError (pub IpAddr);

impl std::error::Error for InvalidNetmaskError {}

impl fmt::Display for InvalidNetmaskError {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format!("invalid netmask ({})", self.0))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidNetmaskPrefixError (pub u8);

impl std::error::Error for InvalidNetmaskPrefixError {}

impl fmt::Display for InvalidNetmaskPrefixError {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format!("invalid netmask prefix ({})", self.0))
    }
}
