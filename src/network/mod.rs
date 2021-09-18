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
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
///
/// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
///
/// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap());
///
/// assert!(network.is_ipv4());
/// assert_eq!(Ok(network), "192.168.0.10/24".parse());
/// assert_eq!(Ok(network), "192.168.0.10/255.255.255.0".parse());
///
/// let netmask = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFF00);
/// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new_with_addr(Ipv6Addr::from(0x1), netmask).unwrap());
///
/// assert!(network.is_ipv6());
/// assert_eq!(Ok(network), "::1/120".parse());
/// assert_eq!(Ok(network), "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00".parse());
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
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 162, 0, 10), 30).unwrap());
    ///
    /// assert_eq!(network.all(), vec![
    ///     Ipv4Addr::new(192, 162, 0, 8),
    ///     Ipv4Addr::new(192, 162, 0, 9),
    ///     Ipv4Addr::new(192, 162, 0, 10),
    ///     Ipv4Addr::new(192, 162, 0, 11)
    /// ]);
    ///
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap());
    ///
    /// assert_eq!(network.all(), vec![
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 3)
    /// ]);
    /// ```
    pub fn all (self) -> Vec<IpAddr> {}

    /// Returns all hosts (exclude network & broadcast addr).
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 162, 0, 10), 30).unwrap());
    ///
    /// assert_eq!(network.hosts(), vec![
    ///     Ipv4Addr::new(192, 162, 0, 9),
    ///     Ipv4Addr::new(192, 162, 0, 10)
    /// ]);
    /// 
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap());
    ///
    /// assert_eq!(network.hosts(), vec![
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1),
    ///     Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2)
    /// ]);
    /// ```
    pub fn hosts (self) -> Vec<IpAddr> {}

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap());
    /// assert_eq!(network.size(), 256);
    ///
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 120).unwrap());
    /// assert_eq!(network.size(), 256);
    /// ```
    pub fn size (&self) -> u128 {}

    /// Returns true if the ip argument is included in the network, else returns false.
    ///
    /// Panic if IPv4 and IPv6 are mixed.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap());
    ///
    /// assert!(network.has(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 0))));
    /// assert!(network.has(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 142))));
    /// assert!(network.has(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 255))));
    ///
    /// assert!(!network.has(IpAddr::V4(Ipv4Addr::new(192, 169, 0, 0))));
    ///
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 64).unwrap());
    ///
    /// assert!(network.has(IpAddr::V6(Ipv6Addr::from(0x1))));
    /// assert!(network.has(IpAddr::V6(Ipv6Addr::from(0xA))));
    /// assert!(network.has(IpAddr::V6(Ipv6Addr::from(0x00FF))));
    ///
    /// assert!(!network.has(IpAddr::V6(Ipv6Addr::from(0xFFFFFFFFFFFFFFFFFF00000000000000))));
    /// ```
    pub fn has (&self, ip: IpAddr) -> bool {}

    /// Returns true if the network contains IPv4, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 162, 0, 10), 30).unwrap())
    /// assert!(network.is_ipv4());
    ///
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap());
    /// assert!(!network.is_ipv4());
    /// ```
    pub fn is_ipv4 (&self) -> bool {}

    /// Returns true if the network contains IPv6, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 126).unwrap());
    /// assert!(network.is_ipv6());
    ///
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 162, 0, 10), 30).unwrap());
    /// assert!(!network.is_ipv6());
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
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork};
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap();
    ///
    /// assert_eq!(IpAddrNetwork::from(network), IpAddrNetwork::V4(network));
    /// ```
    fn from (network: Ipv4AddrNetwork) -> IpAddrNetwork {}
}

impl From<Ipv6AddrNetwork> for IpAddrNetwork {
    /// Create an `IpAddrNetwork::V6` from an `Ipv6AddrNetwork`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::{IpAddrNetwork, Ipv6AddrNetwork};
    ///
    /// let network = Ipv6AddrNetwork::try_new(Ipv6Addr::from(0x1), 120).unwrap();
    ///
    /// assert_eq!(IpAddrNetwork::from(network), IpAddrNetwork::V6(network));
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
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};
    ///
    /// let ip = Ipv4Addr::new(192, 168, 0, 0);
    /// let network = IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(ip, 24).unwrap());
    ///
    /// assert_eq!(Ok(network), "192.168.0.0/24".parse());
    /// assert_eq!(Ok(network), "192.168.0.0/255.255.255.0".parse());
    ///
    /// let ip = Ipv6Addr::new(0xFFFF, 0, 0, 0, 0, 0, 0, 0xFF);
    /// let network = IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(ip, 120).unwrap());
    ///
    /// assert_eq!(Ok(network), "ffff::ff/120".parse());
    /// assert_eq!(Ok(network), "ffff::ff/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00".parse());
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

#[cfg(test)]
mod test {
    use std::net::{Ipv4Addr, Ipv6Addr};

    use crate::{
        IpAddrNetwork,
        Ipv4AddrNetwork,
        Ipv6AddrNetwork,
        NetAddsError,
        NetworkAddrParseError,
        InvalidNetmaskPrefixError
    };

    #[test]
    fn from_str_ip_addr_v4_network () {
        let ip = Ipv4Addr::new(192, 168, 0, 10);

        let network = Ok(IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(ip, 0).unwrap()));
        assert_eq!(network, "192.168.0.10/0".parse());
        assert_eq!(network, "192.168.0.10/0.0.0.0".parse());

        let network = Ok(IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(ip, 24).unwrap()));
        assert_eq!(network, "192.168.0.10/255.255.255.0".parse());
        assert_eq!(network, "192.168.0.10/24".parse());

        let network = Ok(IpAddrNetwork::V4(Ipv4AddrNetwork::try_new(ip, 32).unwrap()));
        assert_eq!(network, "192.168.0.10/255.255.255.255".parse());
        assert_eq!(network, "192.168.0.10/32".parse());

        let err = Err(NetAddsError::NetworkAddrParse(NetworkAddrParseError()));

        // invalid prefix.
        assert_eq!(err, "0.0.0.1/33".parse::<IpAddrNetwork>());

        // ip is out of range.
        assert_eq!(err, "256.0.0.1/24".parse::<IpAddrNetwork>());

        // ip is to short.
        assert_eq!(err, "127.0.0/24".parse::<IpAddrNetwork>());

        // no netmask.
        assert_eq!(err, "127.0.0.1".parse::<IpAddrNetwork>());

        // too many ip.
        assert_eq!(err, "255.0.0.1/255.255.255.0/255.255.255.0".parse::<IpAddrNetwork>());

        // no ip before `/`.
        assert_eq!(err, "/24".parse::<IpAddrNetwork>());

        // no netmask after `/`.
        assert_eq!(err, "127.0.0.1/".parse::<IpAddrNetwork>());
    }

    #[test]
    fn from_str_ip_addr_v6_network () {
        let ip = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);

        let network = Ok(IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(ip, 0).unwrap()));
        assert_eq!(network, "::1/0".parse());
        assert_eq!(network, "::1/::".parse());
        assert_eq!(network, "::1/0:0:0:0:0:0:0:0".parse());
        assert_eq!(network, "::1/0000:0000:0000:0000:0000:0000:0000:0000".parse());
        assert_eq!(network, "::1/0000:0000:0000::0000:0000".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/0".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/::".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/0000:0000:0000::0000:0000".parse());

        let network = Ok(IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(ip, 96).unwrap()));
        assert_eq!(network, "::1/96".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff:0000:0000".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff::".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/96".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff:0000:0000".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff::".parse());

        let network = Ok(IpAddrNetwork::V6(Ipv6AddrNetwork::try_new(ip, 128).unwrap()));
        assert_eq!(network, "::1/128".parse());
        assert_eq!(network, "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/128".parse());
        assert_eq!(network, "0:0:0:0:0:0:0:1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff".parse());

        // invalid prefix.
        let err = Err(NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError(129)));
        assert_eq!(err, "::1/129".parse::<IpAddrNetwork>());

        let err = Err(NetAddsError::NetworkAddrParse(NetworkAddrParseError()));

        // ip is out of range (invalid char "z").
        assert_eq!(err, "::fffz/24".parse::<IpAddrNetwork>());

        // ip is to short.
        assert_eq!(err, "0:0:0:0:0:0:0/24".parse::<IpAddrNetwork>());

        // no netmask.
        assert_eq!(err, "::1".parse::<IpAddrNetwork>());

        // too many ip.
        let s = "::1/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ff00/ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff";
        assert_eq!(err, s.parse::<IpAddrNetwork>());
        
        // no ip before `/`.
        assert_eq!(err, "/128".parse::<IpAddrNetwork>());

        // no netmask after `/`.
        assert_eq!(err, "::1/".parse::<IpAddrNetwork>());
    }
}
