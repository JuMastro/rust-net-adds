use std::convert::TryFrom;
use std::fmt;
use std::net::Ipv6Addr;
use std::str::FromStr;

use crate::errors::NetAddsError;

/// An IPv6 address network.
///
/// See [`crate::IpAddrNetwork`] for a type encompassing both IPv4 and IPv6 network.
///
/// The size of an `Ipv6AddrNetwork` struct may vary depending on the target operating
/// system.
///
/// # Textual representation
///
/// `Ipv6AddrNetwork` provides a [`FromStr`] implementation. The two parts are divided by `/`.
/// The first part must contain an IPv6. The second part can either contain an IPv6 or an u8
/// between 0 and 128 which is valid as a netmask prefix.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ipv6AddrNetwork {
    ip: Ipv6Addr,
    prefix: u8,
    netmask: Ipv6Addr,
    network: Ipv6Addr,
    broadcast: Ipv6Addr
}

impl Ipv6AddrNetwork {
    /// The max network size (netmask prefix).
    const MAX_SHORT_MASK_VALUE: u8 = 128;

    /// Returns an IPv4 network.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    pub fn try_new (ip: Ipv6Addr, prefix: u8) -> Result<Ipv6AddrNetwork, NetAddsError> {}

    /// Returns an IPv4 network.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    pub fn try_new_with_addr (ip: Ipv6Addr, netmask: Ipv6Addr) -> Result<Ipv6AddrNetwork, NetAddsError> {}

    /// Returns the ip addr.
    pub fn ip (self) -> Ipv6Addr {
        self.ip
    }

    /// Returns the netmask prefix.
    pub fn prefix (self) -> u8 {
        self.prefix
    }

    /// Returns the netmask addr.
    pub fn netmask (self) -> Ipv6Addr {
        self.netmask
    }

    /// Returns the network addr.
    pub fn network (self) -> Ipv6Addr {
        self.network
    }

    /// Returns the broadcast addr.
    pub fn broadcast (self) -> Ipv6Addr {
        self.broadcast
    }

    /// Returns all ip of the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn all (&self) -> Vec<Ipv6Addr> {}

    /// Returns all hosts (exclude network & broadcast addr).
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn hosts (&self) -> Vec<Ipv6Addr> {}

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the network, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn has (&self, ip: Ipv6Addr) -> bool {}

    /// Check the validity of a netmask under Ipv6Addr representation.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn validate_netmask (netmask: u128) -> Result<u128, NetAddsError> {}

    /// Check the validity of a netmask under CIDR prefix representation.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn validate_prefix (prefix: u8) -> Result<u8, NetAddsError> {}

    /// Returns the Ipv6Addr representation of a CIDR prefix.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn prefix_to_ip (prefix: u8) -> Result<Ipv6Addr, NetAddsError> {}

    /// Returns the CIDR prefix representation of an Ipv6Addr. 
    ///
    /// If the netmask IPv6 is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    pub fn ip_to_prefix (ip: u128) -> Result<u8, NetAddsError> {}
}

impl fmt::Display for Ipv6AddrNetwork {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", &self.ip(), &self.prefix())
    }
}

impl TryFrom<(Ipv6Addr, u8)> for Ipv6AddrNetwork {
    type Error = NetAddsError;

    /// Create an `Ipv6AddrNetwork` from a tuple of two slots, `Ipv6Addr` and `u8`.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn try_from ((ip, prefix): (Ipv6Addr, u8)) -> Result<Ipv6AddrNetwork, Self::Error> {}
}

impl TryFrom<(Ipv6Addr, Ipv6Addr)> for Ipv6AddrNetwork {
    type Error = NetAddsError;

    /// Create an `Ipv6AddrNetwork` from a tuple of two `Ipv6Addr`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn try_from (ips: (Ipv6Addr, Ipv6Addr)) -> Result<Ipv6AddrNetwork, Self::Error> {}
}

impl FromStr for Ipv6AddrNetwork {
    type Err = NetAddsError;

    /// Parse a string as `Ipv6AddrNetwork`.
    ///
    /// If the string representation is not valid return an `NetAddsError::NetworkAddrParse(NetworkAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}
