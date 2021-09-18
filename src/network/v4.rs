use std::convert::TryFrom;
use std::fmt;
use std::net::Ipv4Addr;
use std::str::FromStr;

use crate::errors::NetAddsError;

/// An IPv4 address network.
///
/// See [`crate::IpAddrNetwork`] for a type encompassing both IPv4 and IPv6 network.
///
/// The size of an `Ipv4AddrNetwork` struct may vary depending on the target operating
/// system.
///
/// # Textual representation
///
/// `Ipv4AddrNetwork` provides a [`FromStr`] implementation. The two parts are divided by `/`.
///  The first part must contain an IPv4. The second part can either contain an IPv4 or an u8 between
///  0 and 32 which is valid as a netmask prefix.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ipv4AddrNetwork {
    ip: Ipv4Addr,
    prefix: u8,
    netmask: Ipv4Addr,
    network: Ipv4Addr,
    broadcast: Ipv4Addr
}

impl Ipv4AddrNetwork {
    /// The max network size (netmask prefix).
    const MAX_SHORT_MASK_VALUE: u8 = 32;

    /// Returns an IPv4 network.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    pub fn try_new (ip: Ipv4Addr, prefix: u8) -> Result<Ipv4AddrNetwork, NetAddsError> {}

    /// Returns an IPv4 network.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    pub fn try_new_with_addr (ip: Ipv4Addr, netmask: Ipv4Addr) -> Result<Ipv4AddrNetwork, NetAddsError> {}

    /// Returns the ip addr.
    pub fn ip (self) -> Ipv4Addr {
        self.ip
    }

    /// Returns the netmask prefix.
    pub fn prefix (self) -> u8 {
        self.prefix
    }

    /// Returns the netmask addr.
    pub fn netmask (self) -> Ipv4Addr {
        self.netmask
    }

    /// Returns the network addr.
    pub fn network (self) -> Ipv4Addr {
        self.network
    }

    /// Returns the broadcast addr.
    pub fn broadcast (self) -> Ipv4Addr {
        self.broadcast
    }

    /// Returns all ip of the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn all (&self) -> Vec<Ipv4Addr> {}

    /// Returns all hosts (exclude network & broadcast addr).
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn hosts (&self) -> Vec<Ipv4Addr> {}

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u32 {}

    /// Returns true if the ip argument is included in the network, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn has (&self, ip: Ipv4Addr) -> bool {}

    /// Check the validity of a netmask under Ipv4Addr representation.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn validate_netmask (netmask: u32) -> Result<u32, NetAddsError> {}

    /// Check the validity of a netmask under CIDR prefix representation.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn validate_prefix (prefix: u8) -> Result<u8, NetAddsError> {}

    /// Returns the Ipv4Addr representation of a CIDR prefix.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn prefix_to_ip (prefix: u8) -> Result<u32, NetAddsError> {}

    /// Returns the CIDR prefix representation of an Ipv4Addr.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn ip_to_prefix (ip: u32) -> Result<u8, NetAddsError> {}
}

impl fmt::Display for Ipv4AddrNetwork {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", &self.ip(), &self.prefix())
    }
}

impl TryFrom<(Ipv4Addr, u8)> for Ipv4AddrNetwork {
    type Error = NetAddsError;

    /// Create an `Ipv4AddrNetwork` from a tuple of two slots, `Ipv4Addr` and `u8`.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn try_from ((ip, prefix): (Ipv4Addr, u8)) -> Result<Ipv4AddrNetwork, Self::Error> {}
}

impl TryFrom<(Ipv4Addr, Ipv4Addr)> for Ipv4AddrNetwork {
    type Error = NetAddsError;

    /// Create an `Ipv4AddrNetwork` from a tuple of two `Ipv4Addr`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn try_from (ips: (Ipv4Addr, Ipv4Addr)) -> Result<Ipv4AddrNetwork, Self::Error> {}
}

impl FromStr for Ipv4AddrNetwork {
    type Err = NetAddsError;

    /// Parse a string as `Ipv4AddrNetwork`.
    ///
    /// If the string representation is not valid return an `NetAddsErrorAddrParse(NetworkAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}
