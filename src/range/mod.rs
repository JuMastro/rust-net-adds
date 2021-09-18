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
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
///
/// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
///
/// let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::new(192, 168, 0, 0), Ipv4Addr::new(192, 168, 0, 255)));
/// assert_eq!(Ok(range), "192.168.0.0-192.168.0.255".parse());
///
/// let range = IpAddrRange::V6(Ipv6AddrRange::new(Ipv6Addr::from(0x1), Ipv6Addr::from(0xFFFF)));
/// assert_eq!(Ok(range), "::1-::ffff".parse());
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IpAddrRange {
    V4(Ipv4AddrRange),
    V6(Ipv6AddrRange)
}

impl IpAddrRange {
    /// Returns the first ip.
    pub fn start (self) -> IpAddr {
        match self {
            IpAddrRange::V4(v4) => IpAddr::V4(v4.start()),
            IpAddrRange::V6(v6) => IpAddr::V6(v6.start())
        }
    }

    /// Returns the last ip.
    pub fn end (self) -> IpAddr {
        match self {
            IpAddrRange::V4(v4) => IpAddr::V4(v4.end()),
            IpAddrRange::V6(v6) => IpAddr::V6(v6.end())
        }
    }

    /// Returns all ips included in the range.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let a = Ipv4Addr::new(0, 0, 0, 0);
    /// let b = Ipv4Addr::new(0, 0, 0, 1);
    /// let c = Ipv4Addr::new(0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V4(Ipv4AddrRange::new(a, c)).all(), vec![
    ///     IpAddr::V4(a),
    ///     IpAddr::V4(b),
    ///     IpAddr::V4(c)
    /// ]);
    ///
    /// let a = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let b = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);
    /// let c = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V6(Ipv6AddrRange::new(c, a)).all(), vec![
    ///     IpAddr::V6(c),
    ///     IpAddr::V6(b),
    ///     IpAddr::V6(a)
    /// ]);
    /// ```
    pub fn all (&self) -> Vec<IpAddr> {
        match self {
            IpAddrRange::V4(rv4) => rv4.all().into_iter().map(IpAddr::V4).collect(),
            IpAddrRange::V6(rv6) => rv6.all().into_iter().map(IpAddr::V6).collect()
        }
    }

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::from(0), Ipv4Addr::from(0xA)));
    /// assert_eq!(range.size(), 11);
    ///
    /// let range = IpAddrRange::V6(Ipv6AddrRange::new(Ipv6Addr::from(0), Ipv6Addr::from(0xA)));
    /// assert_eq!(range.size(), 11);
    /// ```
    pub fn size (&self) -> u128 {
        match self {
            IpAddrRange::V4(v4) => u128::from(v4.size()),
            IpAddrRange::V6(v6) => v6.size()
        }
    }

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Panic if IPv4 and IPv6 are mixed.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::from(0), Ipv4Addr::from(0xA)));
    /// assert!(range.has(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0))));
    /// assert!(range.has(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 5))));
    /// assert!(range.has(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 10))));
    ///
    /// assert!(!range.has(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 11))));
    ///
    /// let range = IpAddrRange::V6(Ipv6AddrRange::new(Ipv6Addr::from(0), Ipv6Addr::from(0xA)));
    /// assert!(range.has(IpAddr::V6(Ipv6Addr::from(0x1))));
    /// assert!(range.has(IpAddr::V6(Ipv6Addr::from(0x5))));
    /// assert!(range.has(IpAddr::V6(Ipv6Addr::from(0xA))));
    ///
    /// assert!(!range.has(IpAddr::V6(Ipv6Addr::from(0xFFFF))));
    /// ```
    pub fn has (&self, ip: IpAddr) -> bool {
        match (self, ip) {
            (IpAddrRange::V4(v4), IpAddr::V4(ipv4)) => v4.has(ipv4),
            (IpAddrRange::V6(v6), IpAddr::V6(ipv6)) => v6.has(ipv6),
            _ => panic!("cannot mix IPv4 and IPv6 to check if range includes ip")
        }
    }

    /// Returns true if the range contains IPv4, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let a = Ipv4Addr::new(0, 0, 0, 0);
    /// let b = Ipv4Addr::new(0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V4(Ipv4AddrRange::new(a, b)).is_ipv4(), true);
    ///
    /// let a = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let b = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V6(Ipv6AddrRange::new(a, b)).is_ipv4(), false);
    /// ```
    pub fn is_ipv4 (&self) -> bool {
        match self {
            IpAddrRange::V4(_) => true,
            IpAddrRange::V6(_) => false
        }
    }

    /// Returns true if the range contains IPv6, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let a = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let b = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V6(Ipv6AddrRange::new(a, b)).is_ipv6(), true);
    ///
    /// let a = Ipv4Addr::new(0, 0, 0, 0);
    /// let b = Ipv4Addr::new(0, 0, 0, 2);
    ///
    /// assert_eq!(IpAddrRange::V4(Ipv4AddrRange::new(a, b)).is_ipv6(), false);
    /// ```
    pub fn is_ipv6 (&self) -> bool {
        match self {
            IpAddrRange::V4(_) => false,
            IpAddrRange::V6(_) => true
        }
    }
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
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange};
    ///
    /// let a = Ipv4Addr::new(0, 0, 0, 0);
    /// let b = Ipv4Addr::new(0, 0, 0, 10);
    ///
    /// assert_eq!(IpAddrRange::from(Ipv4AddrRange::new(a, b)), IpAddrRange::V4(Ipv4AddrRange::new(a, b)));
    /// ```
    fn from (range: Ipv4AddrRange) -> IpAddrRange {
        IpAddrRange::V4(range)
    }
}

impl From<Ipv6AddrRange> for IpAddrRange {
    /// Create an `IpAddrRange::V6` from an `Ipv6AddrRange`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::{IpAddrRange, Ipv6AddrRange};
    ///
    /// let a = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let b = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0xa);
    /// let range = Ipv6AddrRange::new(a, b);
    /// assert_eq!(IpAddrRange::from(range), IpAddrRange::V6(range));
    /// ```
    fn from (range: Ipv6AddrRange) -> IpAddrRange {
        IpAddrRange::V6(range)
    }
}

impl FromStr for IpAddrRange {
    type Err = NetAddsError;

    /// Parse a string as `IpAddrRange`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};
    ///
    /// let a = Ipv4Addr::new(192, 168, 0, 0);
    /// let b = Ipv4Addr::new(192, 168, 0, 255);
    /// let range = IpAddrRange::V4(Ipv4AddrRange::new(a, b));
    /// assert_eq!("192.168.0.0-192.168.0.255".parse(), Ok(range));
    ///
    /// let a = Ipv6Addr::new(0xFFFF, 0, 0, 0, 0, 0, 0, 0xFF);
    /// let b = Ipv6Addr::new(0xFFFF, 0, 0, 0, 0, 0, 0, 0xFFFF);
    /// let range = IpAddrRange::V6(Ipv6AddrRange::new(a, b));
    /// assert_eq!("ffff::ff-ffff::ffff".parse(), Ok(range));
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {
        Ipv4AddrRange::from_str(s)
            .map(IpAddrRange::V4)
            .or_else(move |_| Ipv6AddrRange::from_str(s).map(IpAddrRange::V6))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RangeAddrParseError ();

impl std::error::Error for RangeAddrParseError {}

impl fmt::Display for RangeAddrParseError {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", "invalid IP address range syntax")
    }
}

#[cfg(test)]
mod test {
    use std::net::{Ipv4Addr, Ipv6Addr};

    use crate::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange, NetAddsError, RangeAddrParseError};

    #[test]
    fn from_str () {
        // IPv4
        let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::new(0, 0, 0, 1), Ipv4Addr::new(0, 0, 0, 10)));
        assert_eq!("0.0.0.1-0.0.0.10".parse(), Ok(range));

        let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::new(0, 0, 0, 0), Ipv4Addr::new(255, 255, 255, 255)));
        assert_eq!("0.0.0.0-255.255.255.255".parse(), Ok(range));

        let range = IpAddrRange::V4(Ipv4AddrRange::new(Ipv4Addr::new(255, 255, 255, 255), Ipv4Addr::new(0, 0, 0, 0)));
        assert_eq!("255.255.255.255-0.0.0.0".parse(), Ok(range));

        let err = Err(NetAddsError::RangeAddrParse(RangeAddrParseError()));

        // one ip is out of range.
        assert_eq!(err, "256.0.0.1-255.0.0.1".parse::<IpAddrRange>());

        // only one ip provided.
        assert_eq!(err, "127.0.0.1".parse::<IpAddrRange>());

        // to many ip provided.
        assert_eq!(err, "255.0.0.1-255.0.0.10-255.0.0.20".parse::<IpAddrRange>());

        // no ip before `-`.
        assert_eq!(err, "-127.0.0.1".parse::<IpAddrRange>());

        // no ip after `-`.
        assert_eq!(err, "127.0.0.1-".parse::<IpAddrRange>());

        // IPv6
        let a = Ipv6Addr::from(0x1);
        let b = Ipv6Addr::from(0xA);
        let range = IpAddrRange::V6(Ipv6AddrRange::new(a, b));
        assert_eq!(Ok(range), "::1-0:0:0:0:0:0:0:a".parse());
        assert_eq!(Ok(range), "0:0:0:0:0:0:0:1-::a".parse());
        assert_eq!(Ok(range), "::1-::a".parse());
        assert_eq!(Ok(range), "0:0:0:0:0:0:0:1-0:0:0:0:0:0:0:a".parse());

        let a = Ipv6Addr::new(0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF);
        let b = Ipv6Addr::from(0);
        let range = Ipv6AddrRange::new(a, b);
        assert_eq!(Ok(range), "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff-0:0:0:0:0:0:0:0".parse());
        assert_eq!(Ok(range), "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff-::".parse());

        let err = Err(NetAddsError::RangeAddrParse(RangeAddrParseError()));

        // one ip is out of range (invalid char "z").
        assert_eq!(err, "::fz-::fffe".parse::<Ipv6AddrRange>());

        // only one ip provided.
        assert_eq!(err, "0:0:0:0:0:0:0:0".parse::<Ipv6AddrRange>());

        // to many ip provided.
        assert_eq!(err, "::-::1-::2".parse::<Ipv6AddrRange>());

        // no ip before `-`.
        assert_eq!(err, "-::1".parse::<Ipv6AddrRange>());

        // no ip after `-`.
        assert_eq!(err, "::1-".parse::<Ipv6AddrRange>());
    }
}
