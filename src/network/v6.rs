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
/// use std::net::Ipv6Addr;
///
/// use net_adds::Ipv6AddrNetwork;
///
/// let ip = Ipv6Addr::from(0x1);
/// let network = Ipv6AddrNetwork::try_new(ip, 120).unwrap();
///
/// assert_eq!(Ok(network), "::1/120".parse());
/// assert_eq!(Ok(network), "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00".parse());
///
/// let netmask = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFF00);
/// let networkb = Ipv6AddrNetwork::try_new_with_addr(ip, netmask).unwrap();
///
/// assert_eq!(networkb, network);
/// assert_eq!(Ok(networkb), "::1/120".parse());
/// assert_eq!(Ok(networkb), "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00".parse());
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
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let network = Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap();
    ///
    /// assert_eq!(network.all(), vec![
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 3)
    /// ]);
    /// ```
    pub fn all (&self) -> Vec<Ipv6Addr> {}

    /// Returns all hosts (exclude network & broadcast addr).
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let network = Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap();
    ///
    /// assert_eq!(network.hosts(), vec![
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2)
    /// ]);
    /// ```
    pub fn hosts (&self) -> Vec<Ipv6Addr> {}

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let network = Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 120).unwrap();
    ///
    /// assert_eq!(network.size(), 256);
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the network, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let network = Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 64).unwrap();
    ///
    /// assert!(network.has(Ipv6Addr::from(0x1)));
    /// assert!(network.has(Ipv6Addr::from(0xA)));
    /// assert!(network.has(Ipv6Addr::from(0x00FF)));
    ///
    /// assert!(!network.has(Ipv6Addr::from(0xFFFFFFFFFFFFFFFFFF00000000000000)));
    /// ```
    pub fn has (&self, ip: Ipv6Addr) -> bool {}

    /// Check the validity of a netmask under Ipv6Addr representation.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let netmask = Ipv6Addr::from(0xFFFFFFFF000000000000000000000000);
    /// assert_eq!(Ipv6AddrNetwork::validate_netmask(u128::from(netmask)), Ok(netmask));
    ///
    /// let netmask = Ipv6Addr::from(0x0000000000000000000000000000FFFF);
    /// assert!(Ipv6AddrNetwork::validate_netmask(u128::from(netmask)).is_err());
    /// ```
    pub fn validate_netmask (netmask: u128) -> Result<u128, NetAddsError> {}

    /// Check the validity of a netmask under CIDR prefix representation.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// assert_eq!(Ipv6AddrNetwork::validate_prefix(128), Ok(128));
    ///
    /// assert!(Ipv6AddrNetwork::validate_prefix(129).is_err());
    /// ```
    pub fn validate_prefix (prefix: u8) -> Result<u8, NetAddsError> {}

    /// Returns the Ipv6Addr representation of a CIDR prefix.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// assert_eq!(Ipv6AddrNetwork::prefix_to_ip(128), Ok(u128::MAX));
    ///
    /// assert!(Ipv6AddrNetwork::prefix_to_ip(129).is_err());
    /// ```
    pub fn prefix_to_ip (prefix: u8) -> Result<u128, NetAddsError> {}

    /// Returns the CIDR prefix representation of an Ipv6Addr. 
    ///
    /// If the netmask IPv6 is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let netmask = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF);
    /// assert_eq!(Ipv6AddrNetwork::ip_to_prefix(u128::from(netmask)), Ok(128));
    ///
    /// let netmask = Ipv6Addr::new(0x0, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF);
    /// assert!(Ipv6AddrNetwork::ip_to_prefix(u128::from(netmask)).is_err());
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
    /// use std::convert::TryFrom;
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let ip = Ipv6Addr::from(0x1);
    ///
    /// assert_eq!(Ipv6AddrNetwork::try_from((ip, 92)), Ipv6AddrNetwork::try_new(ip, 92));
    ///
    /// assert!(Ipv6AddrNetwork::try_from((ip, 129)).is_err());
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
    /// use std::convert::TryFrom;
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let ip = Ipv6Addr::from(1);
    ///
    /// let netmask = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFF00);
    /// assert_eq!(Ipv6AddrNetwork::try_from((ip, netmask)), Ipv6AddrNetwork::try_new_with_addr(ip, netmask));
    ///
    /// let netmask = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0x2002);
    /// assert!(Ipv6AddrNetwork::try_from((ip, netmask)).is_err());
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
    /// use std::convert::TryFrom;
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrNetwork;
    ///
    /// let network = Ipv6AddrNetwork::try_from((Ipv6Addr::from(1), 126)).expect("invalid network");
    ///
    /// assert_eq!("::1/126".parse(), Ok(network));
    /// assert_eq!("::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:fffc".parse(), Ok(network));
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}

#[cfg(test)]
mod test {
    use std::net::Ipv6Addr;

    use crate::{Ipv6AddrNetwork, NetAddsError, NetworkAddrParseError, InvalidNetmaskPrefixError};

    #[test]
    fn from_str () {
        let ip = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);

        let network = Ipv6AddrNetwork::try_new(ip, 0);
        assert_eq!(network, "::1/0".parse());
        assert_eq!(network, "::1/::".parse());
        assert_eq!(network, "::1/0:0:0:0:0:0:0:0".parse());
        assert_eq!(network, "::1/0000:0000:0000:0000:0000:0000:0000:0000".parse());
        assert_eq!(network, "::1/0000:0000:0000::0000:0000".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/0".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/::".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/0000:0000:0000::0000:0000".parse());

        let network = Ipv6AddrNetwork::try_new(ip, 96);
        assert_eq!(network, "::1/96".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff:0000:0000".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff::".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/96".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff:0000:0000".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff::".parse());

        let network = Ipv6AddrNetwork::try_new(ip, 128);
        assert_eq!(network, "::1/128".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/128".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff".parse());

        // invalid prefix.
        let err = Err(NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError(129)));
        assert_eq!(err, "::1/129".parse::<Ipv6AddrNetwork>());

        let err = Err(NetAddsError::NetworkAddrParse(NetworkAddrParseError()));

        // ip is out of range (invalid char "z").
        assert_eq!(err, "::fffz/24".parse::<Ipv6AddrNetwork>());

        // ip is to short.
        assert_eq!(err, "0:0:0:0:0:0:0/24".parse::<Ipv6AddrNetwork>());

        // no netmask.
        assert_eq!(err, "::1".parse::<Ipv6AddrNetwork>());

        // too many ip.
        let s = "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff";
        assert_eq!(err, s.parse::<Ipv6AddrNetwork>());

        // no ip before `/`.
        assert_eq!(err, "/128".parse::<Ipv6AddrNetwork>());

        // no netmask after `/`.
        assert_eq!(err, "::1/".parse::<Ipv6AddrNetwork>());
    }
}
