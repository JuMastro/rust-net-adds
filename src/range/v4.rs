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
/// use std::net::Ipv4Addr;
///
/// use net_adds::Ipv4AddrRange;
///
/// let a = Ipv4Addr::new(192, 168, 0, 0);
/// let b = Ipv4Addr::new(192, 168, 0, 255);
/// let range = Ipv4AddrRange::new(a, b);
///
/// assert_eq!(Ok(range), "192.168.0.0-192.168.0.255".parse());
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
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrRange;
    ///
    /// let a = Ipv4Addr::new(0, 0, 0, 0);
    /// let b = Ipv4Addr::new(0, 0, 0, 1);
    /// let c = Ipv4Addr::new(0, 0, 0, 2);
    ///
    /// assert_eq!(Ipv4AddrRange::new(a, c).all(), vec![a, b, c]);
    /// assert_eq!(Ipv4AddrRange::new(c, a).all(), vec![c, b, a]);
    /// assert_eq!(Ipv4AddrRange::new(a, a).all(), vec![a]);
    /// ```
    pub fn all (&self) -> Vec<Ipv4Addr> {}

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrRange;
    ///
    /// let a = Ipv4Addr::new(192, 168, 0, 0);
    /// let b = Ipv4Addr::new(192, 168, 0, 10);
    ///
    /// let range = Ipv4AddrRange::new(a, b);
    /// assert_eq!(range.size(), 11);
    ///
    /// let range = Ipv4AddrRange::new(b, a);
    /// assert_eq!(range.size(), 11);
    /// ```
    pub fn size (&self) -> u32 {}

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrRange;
    ///
    /// let a = Ipv4Addr::new(192, 168, 0, 0);
    /// let b = Ipv4Addr::new(192, 168, 0, 255);
    ///
    /// let range = Ipv4AddrRange::new(a, b);
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 0)));
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 142)));
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 255)));
    ///
    /// assert!(!range.has(Ipv4Addr::new(192, 169, 0, 0)));
    ///
    /// let range = Ipv4AddrRange::new(b, a);
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 0)));
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 142)));
    /// assert!(range.has(Ipv4Addr::new(192, 168, 0, 255)));
    ///
    /// assert!(!range.has(Ipv4Addr::new(192, 169, 0, 0)));
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
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrRange;
    ///
    /// let start = Ipv4Addr::new(0, 0, 0, 0);
    /// let end = Ipv4Addr::new(0, 0, 0, 10);
    ///
    /// assert_eq!(Ipv4AddrRange::from((start, end)), Ipv4AddrRange::new(start, end));
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
    /// use std::net::Ipv4Addr;
    ///
    /// use net_adds::Ipv4AddrRange;
    ///
    /// let range = Ipv4AddrRange::new(Ipv4Addr::new(192, 168, 0, 0), Ipv4Addr::new(192, 168, 0, 255));
    ///
    /// assert_eq!("192.168.0.0-192.168.0.255".parse(), Ok(range));
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {}
}

#[cfg(test)]
mod test {
    use std::net::Ipv4Addr;

    use crate::{Ipv4AddrRange, NetAddsError, RangeAddrParseError};

    #[test]
    fn from_str () {
        let range = Ipv4AddrRange::new(Ipv4Addr::new(0, 0, 0, 1), Ipv4Addr::new(0, 0, 0, 10));
        assert_eq!("0.0.0.1-0.0.0.10".parse(), Ok(range));

        let range = Ipv4AddrRange::new(Ipv4Addr::new(0, 0, 0, 0), Ipv4Addr::new(255, 255, 255, 255));
        assert_eq!("0.0.0.0-255.255.255.255".parse(), Ok(range));

        let range = Ipv4AddrRange::new(Ipv4Addr::new(255, 255, 255, 255), Ipv4Addr::new(0, 0, 0, 0));
        assert_eq!("255.255.255.255-0.0.0.0".parse(), Ok(range));

        let err = Err(NetAddsError::RangeAddrParse(RangeAddrParseError()));

        // one ip is out of range.
        assert_eq!(err, "256.0.0.1-255.0.0.1".parse::<Ipv4AddrRange>());

        // only one ip provided.
        assert_eq!(err, "127.0.0.1".parse::<Ipv4AddrRange>());

        // to many ip provided.
        assert_eq!(err, "255.0.0.1-255.0.0.10-255.0.0.20".parse::<Ipv4AddrRange>());

        // no ip before `-`.
        assert_eq!(err, "-127.0.0.1".parse::<Ipv4AddrRange>());

        // no ip after `-`.
        assert_eq!(err, "127.0.0.1-".parse::<Ipv4AddrRange>());
    }
}
