use std::convert::TryFrom;
use std::fmt;
use std::net::{IpAddr, Ipv4Addr};
use std::str::FromStr;
use std::vec::IntoIter;

use crate::errors::NetAddsError;
use crate::range::Ipv4AddrRange;
use crate::network::{NetworkAddrParseError, InvalidNetmaskError, InvalidNetmaskPrefixError};
use crate::iter::{IntoSmartIterator, Ipv4AddrSmartIterator};

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
///  The first part must contain an IPv4. The second part can either contain an IPv4 or an u8
/// between 0 and 32 which is valid as a netmask prefix.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// use std::net::Ipv4Addr;
///
/// use net_adds::Ipv4AddrNetwork;
///
/// let ip = Ipv4Addr::new(192, 168, 0, 10);
/// let network = Ipv4AddrNetwork::try_new(ip, 24).unwrap();
///
/// assert_eq!(Ok(network), "192.168.0.10/255.255.255.0".parse());
/// assert_eq!(Ok(network), "192.168.0.10/24".parse());
///
/// let netmask = Ipv4Addr::new(255, 255, 255, 0);
/// let networkb = Ipv4AddrNetwork::try_new_with_addr(ip, netmask).unwrap();
///
/// assert_eq!(networkb, network);
/// assert_eq!(Ok(networkb), "192.168.0.10/255.255.255.0".parse());
/// assert_eq!(Ok(networkb), "192.168.0.10/24".parse());
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
    pub fn try_new (ip: Ipv4Addr, prefix: u8) -> Result<Ipv4AddrNetwork, NetAddsError> {
        let iu = u32::from(ip);
        let nu = Self::prefix_to_ip(prefix)?;
        let netmask = Ipv4Addr::from(nu);
        let network = Ipv4Addr::from(iu & nu);
        let broadcast = Ipv4Addr::from(iu | !nu);
        Ok(Ipv4AddrNetwork { ip, prefix, netmask, network, broadcast })
    }

    /// Returns an IPv4 network.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    pub fn try_new_with_addr (ip: Ipv4Addr, netmask: Ipv4Addr) -> Result<Ipv4AddrNetwork, NetAddsError> {
        let iu = u32::from(ip);
        let nu = u32::from(netmask);
        let prefix = Self::ip_to_prefix(nu)?;
        let network = Ipv4Addr::from(iu & nu);
        let broadcast = Ipv4Addr::from(iu | !nu);
        Ok(Ipv4AddrNetwork { ip, prefix, netmask, network, broadcast })
    }

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
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 30).unwrap();
    ///
    /// assert_eq!(network.all(), vec![
    ///     Ipv4Addr::new(192, 168, 0, 8),
    ///     Ipv4Addr::new(192, 168, 0, 9),
    ///     Ipv4Addr::new(192, 168, 0, 10),
    ///     Ipv4Addr::new(192, 168, 0, 11)
    /// ]);
    /// ```
    pub fn all (&self) -> Vec<Ipv4Addr> {
        Ipv4AddrRange::new(self.network(), self.broadcast()).all()
    }

    /// Returns all hosts (exclude network & broadcast addr).
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 30).unwrap();
    ///
    /// assert_eq!(network.hosts(), vec![
    ///     Ipv4Addr::new(192, 168, 0, 9),
    ///     Ipv4Addr::new(192, 168, 0, 10)
    /// ]);
    /// ```
    pub fn hosts (&self) -> Vec<Ipv4Addr> {
        let mut ips = Ipv4AddrRange::new(self.network(), self.broadcast()).all();
        ips.remove(0);
        ips.pop();
        ips
    }

    /// Returns the number of ip's included in the network including the network and the broadcast addr.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap();
    ///
    /// assert_eq!(network.size(), 256);
    /// ```
    pub fn size (&self) -> u32 {
        u32::from(self.broadcast()) - u32::from(self.network()) + 1
    }

    /// Returns true if the ip argument is included in the network, else returns false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24).unwrap();
    ///
    /// assert!(network.has(Ipv4Addr::new(192, 168, 0, 0)));
    /// assert!(network.has(Ipv4Addr::new(192, 168, 0, 142)));
    /// assert!(network.has(Ipv4Addr::new(192, 168, 0, 255)));
    ///
    /// assert!(!network.has(Ipv4Addr::new(192, 169, 0, 0)));
    /// ```
    pub fn has (&self, ip: Ipv4Addr) -> bool {
        let needle = u32::from(ip);
        let network = u32::from(self.network());
        let broadcast = u32::from(self.broadcast());
        return needle >= network && needle <= broadcast
    }

    /// Check the validity of a netmask under Ipv4Addr representation.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let netmask = Ipv4Addr::new(255, 255, 255, 0);
    /// assert_eq!(Ipv4AddrNetwork::validate_netmask(u32::from(netmask)), Ok(u32::from(netmask)));
    ///
    /// let netmask = Ipv4Addr::new(0, 0, 0, 255);
    /// assert!(Ipv4AddrNetwork::validate_netmask(u32::from(netmask)).is_err());
    /// ```
    pub fn validate_netmask (netmask: u32) -> Result<u32, NetAddsError> {
        if netmask != 0 && (((!netmask + 1) & !netmask) != 0) {
            Err(NetAddsError::InvalidNetmask(InvalidNetmaskError(IpAddr::V4(Ipv4Addr::from(netmask)))))
        } else {
            Ok(netmask)
        }
    }

    /// Check the validity of a netmask under CIDR prefix representation.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// assert_eq!(Ipv4AddrNetwork::validate_prefix(32), Ok(32));
    ///
    /// assert!(Ipv4AddrNetwork::validate_prefix(33).is_err());
    /// ```
    pub fn validate_prefix (prefix: u8) -> Result<u8, NetAddsError> {
        if prefix > Self::MAX_SHORT_MASK_VALUE {
            Err(NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError(prefix)))
        } else {
            Ok(prefix)
        }
    }

    /// Returns the Ipv4Addr representation of a CIDR prefix.
    ///
    /// If the netmask prefix is not valid return an `NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// assert_eq!(Ipv4AddrNetwork::prefix_to_ip(0), Ok(0));
    /// assert_eq!(Ipv4AddrNetwork::prefix_to_ip(32), Ok(u32::MAX));
    ///
    /// assert!(Ipv4AddrNetwork::prefix_to_ip(33).is_err());
    /// ```
    pub fn prefix_to_ip (prefix: u8) -> Result<u32, NetAddsError> {
        if Self::validate_prefix(prefix)? == 0 {
            Ok(0)
        } else {
            Ok((u32::MAX << (32 - prefix)) & u32::MAX)
        }
    }

    /// Returns the CIDR prefix representation of an Ipv4Addr.
    ///
    /// We count the bit that are equals to 0 by shifting the sequence to the right (bitwise >>).
    /// Then we subtract the number of bits equal to 0 from the maximum number of bits available on the netmask.
    ///
    /// If the netmask is not valid return an `NetAddsError::InvalidNetmask(InvalidNetmaskError)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// assert_eq!(Ipv4AddrNetwork::ip_to_prefix(u32::from(Ipv4Addr::new(0, 0, 0, 0))), Ok(0));
    /// assert_eq!(Ipv4AddrNetwork::ip_to_prefix(u32::from(Ipv4Addr::new(255, 255, 255, 255))), Ok(32));
    ///
    /// assert!(Ipv4AddrNetwork::ip_to_prefix(u32::from(Ipv4Addr::new(0, 255, 255, 255))).is_err());
    /// ```
    pub fn ip_to_prefix (ip: u32) -> Result<u8, NetAddsError> {
        if Self::validate_netmask(ip)? == 0 {
            Ok(0)
        } else {
            let mut tmp = ip.clone();
            let mut bits = 0;
            while (tmp & 0x1) == 0 {
                tmp = tmp >> 1;
                bits = bits + 1;
            }
            Ok(u8::try_from(Self::MAX_SHORT_MASK_VALUE - bits).unwrap())
        }
    }
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
    /// # Examples:
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let ip = Ipv4Addr::new(192, 168, 0, 10);
    ///
    /// assert_eq!(Ipv4AddrNetwork::try_from((ip, 24)), Ipv4AddrNetwork::try_new(ip, 24));
    ///
    /// assert!(Ipv4AddrNetwork::try_from((ip, 33)).is_err());
    /// ```
    fn try_from ((ip, prefix): (Ipv4Addr, u8)) -> Result<Ipv4AddrNetwork, Self::Error> {
        Ipv4AddrNetwork::try_new(ip, prefix)
    }
}

impl TryFrom<(Ipv4Addr, Ipv4Addr)> for Ipv4AddrNetwork {
    type Error = NetAddsError;

    /// Create an `Ipv4AddrNetwork` from a tuple of two `Ipv4Addr`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let ip = Ipv4Addr::new(192, 168, 0, 10);
    ///
    /// let netmask = Ipv4Addr::new(255, 255, 255, 0);
    /// assert_eq!(Ipv4AddrNetwork::try_from((ip, netmask)), Ipv4AddrNetwork::try_new(ip, 24));
    ///
    /// let netmask = Ipv4Addr::new(255, 255, 117, 0);
    /// assert!(Ipv4AddrNetwork::try_from((ip, netmask)).is_err());
    /// ```
    fn try_from (ips: (Ipv4Addr, Ipv4Addr)) -> Result<Ipv4AddrNetwork, Self::Error> {
        Ipv4AddrNetwork::try_new_with_addr(ips.0, ips.1)
    }
}

impl FromStr for Ipv4AddrNetwork {
    type Err = NetAddsError;

    /// Parse a string as `Ipv4AddrNetwork`.
    ///
    /// If the string representation is not valid return an `NetAddsErrorAddrParse(NetworkAddrParseError)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 10), 24);
    ///
    /// assert_eq!("192.168.0.10/24".parse(), network);
    /// assert_eq!("192.168.0.10/255.255.255.0".parse(), network);
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {
        let mut parts = s.split('/');

        let ip = parts.next().map(|part| {
            Ipv4Addr::from_str(part)
                .map_err(|_| NetAddsError::NetworkAddrParse(NetworkAddrParseError()))
        });

        let netmask = parts.next().map(|part| {
            Ipv4Addr::from_str(part).or(
                part.parse::<u8>()
                    .map_err(|_| NetAddsError::NetworkAddrParse(NetworkAddrParseError()))
                    .and_then(|prefix| Ok(Ipv4Addr::from(Self::prefix_to_ip(prefix)?)))
            )
        });

        if ip.is_none() || netmask.is_none() || parts.next().is_some() {
            Err(NetAddsError::NetworkAddrParse(NetworkAddrParseError()))
        } else {
            Ipv4AddrNetwork::try_new_with_addr(ip.unwrap()?, netmask.unwrap()?)
        }
    }
}

impl IntoIterator for Ipv4AddrNetwork {
    type Item = Ipv4Addr;
    type IntoIter = IntoIter<Self::Item>;

    /// Create a `Ipv4Addr` iterator. The iterator include the network and the broadcast.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrNetwork;
    ///
    /// let mut iter = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 0), 30)
    ///     .expect("invalid network")
    ///     .into_iter();
    ///
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 0)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 1)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 2)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn into_iter (self) -> Self::IntoIter {
        self.all().into_iter()
    }
}

impl IntoSmartIterator for Ipv4AddrNetwork {
    type Item = Ipv4Addr;
    type IntoSmartIter = Ipv4AddrSmartIterator;

    /// Create a smart `Ipv4Addr` iterator. The iterator include the network and the broadcast.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::{Ipv4AddrNetwork, IntoSmartIterator};
    ///
    /// let mut iter = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 0), 30)
    ///     .expect("invalid network")
    ///     .into_smart_iter();
    ///
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 0)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 1)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 2)));
    /// assert_eq!(iter.next(), Some(Ipv4Addr::new(192, 168, 0, 3)));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn into_smart_iter (self) -> Self::IntoSmartIter {
        Ipv4AddrSmartIterator::new(self.network(), self.broadcast())
    }
}

#[cfg(test)]
mod test {
    use std::net::Ipv4Addr;

    use crate::{Ipv4AddrNetwork, NetAddsError, NetworkAddrParseError, InvalidNetmaskPrefixError};

    #[test]
    fn from_str () {
        let ip = Ipv4Addr::new(192, 168, 0, 10);

        let network = Ipv4AddrNetwork::try_new(ip, 0);
        assert_eq!(network, "192.168.0.10/0".parse());
        assert_eq!(network, "192.168.0.10/0.0.0.0".parse());

        let network = Ipv4AddrNetwork::try_new(ip, 24);
        assert_eq!(network, "192.168.0.10/24".parse());
        assert_eq!(network, "192.168.0.10/255.255.255.0".parse());

        let network = Ipv4AddrNetwork::try_new(ip, 32);
        assert_eq!(network, "192.168.0.10/32".parse());
        assert_eq!(network, "192.168.0.10/255.255.255.255".parse());

        // invalid prefix.
        let err = Err(NetAddsError::InvalidNetmaskPrefix(InvalidNetmaskPrefixError(33)));
        assert_eq!(err, "0.0.0.1/33".parse::<Ipv4AddrNetwork>());

        let err = Err(NetAddsError::NetworkAddrParse(NetworkAddrParseError()));

        // ip is out of range.
        assert_eq!(err, "256.0.0.1/24".parse::<Ipv4AddrNetwork>());

        // ip is to short.
        assert_eq!(err, "127.0.0/24".parse::<Ipv4AddrNetwork>());

        // no netmask.
        assert_eq!(err, "127.0.0.1".parse::<Ipv4AddrNetwork>());

        // too many ip.
        assert_eq!(err, "255.0.0.1/255.255.255.0/255.255.255.0".parse::<Ipv4AddrNetwork>());

        // no ip before `/`.
        assert_eq!(err, "/24".parse::<Ipv4AddrNetwork>());

        // no netmask after `/`.
        assert_eq!(err, "127.0.0.1/".parse::<Ipv4AddrNetwork>());
    }
}
