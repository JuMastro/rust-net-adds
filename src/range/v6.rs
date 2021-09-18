use std::fmt;
use std::net::Ipv6Addr;
use std::str::FromStr;

use crate::errors::NetAddsError;
use crate::range::RangeAddrParseError;

/// An IPv6 address range.
///
/// See [`crate::IpAddrRange`] for a type encompassing both IPv4 and IPv6 range.
///
/// The size of an `Ipv6AddrRange` struct may vary depending on the target operating
/// system.
///
/// # Textual representation
///
/// `Ipv6AddrRange` provides a [`FromStr`] implementation.
/// The two parts are represented by Ipv6Addr and are separated by '-'.
///
/// [`FromStr`]: std::str::FromStr
///
/// # Examples
///
/// ```
/// use std::net::Ipv6Addr;
///
/// use net_adds::Ipv6AddrRange;
///
/// let a = Ipv6Addr::from(0x1);
/// let b = Ipv6Addr::from(0xA);
/// let range = Ipv6AddrRange::new(a, b);
///
/// assert_eq!(Ok(range), "::1-::A".parse());
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ipv6AddrRange {
    start: Ipv6Addr,
    end: Ipv6Addr
}

impl Ipv6AddrRange {
    /// Returns an `Ipv6AddrRange`.
    pub fn new (start: Ipv6Addr, end: Ipv6Addr) -> Ipv6AddrRange {
        Ipv6AddrRange { start, end }
    }

    /// Returns the first ip. 
    pub fn start (self) -> Ipv6Addr {
        self.start
    }

    /// Returns the last ip.
    pub fn end (self) -> Ipv6Addr {
        self.end
    }

    /// Returns all ips included in the range.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrRange;
    ///
    /// let a = Ipv6Addr::from(0x1);
    /// let b = Ipv6Addr::from(0x2);
    /// let c = Ipv6Addr::from(0x3);
    ///
    /// assert_eq!(Ipv6AddrRange::new(a, c).all(), vec![a, b, c]);
    /// assert_eq!(Ipv6AddrRange::new(c, a).all(), vec![c, b, a]);
    /// assert_eq!(Ipv6AddrRange::new(a, a).all(), vec![a]);
    /// ```
    pub fn all (&self) -> Vec<Ipv6Addr> {
        if self.start <= self.end {
            (u128::from(self.start)..=u128::from(self.end)).map(Ipv6Addr::from).collect()
        } else {
            (u128::from(self.end)..=u128::from(self.start)).map(Ipv6Addr::from).rev().collect()
        }
    }

    /// Returns the number of ip's included in the range.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrRange;
    ///
    /// let a = Ipv6Addr::from(0x0);
    /// let b = Ipv6Addr::from(0xA);
    ///
    /// let range = Ipv6AddrRange::new(a, b);
    /// assert_eq!(range.size(), 11);
    ///
    /// let range = Ipv6AddrRange::new(b, a);
    /// assert_eq!(range.size(), 11);
    /// ```
    pub fn size (&self) -> u128 {
        let start = u128::from(self.start());
        let end = u128::from(self.end());
        if start < end {
            end - start + 1
        } else {
            start - end + 1
        }
    }

    /// Returns true if the ip argument is included in the range, else returns false.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrRange;
    ///
    /// let a = Ipv6Addr::from(0x0);
    /// let b = Ipv6Addr::from(0xA);
    ///
    /// let range = Ipv6AddrRange::new(a, b);
    ///
    /// assert!(range.has(Ipv6Addr::from(0x0)));
    /// assert!(range.has(Ipv6Addr::from(0x2)));
    /// assert!(range.has(Ipv6Addr::from(0xA)));
    ///
    /// assert!(!range.has(Ipv6Addr::from(0xFFFF)));
    ///
    /// let range = Ipv6AddrRange::new(b, a);
    ///
    /// assert!(range.has(Ipv6Addr::from(0x0)));
    /// assert!(range.has(Ipv6Addr::from(0x2)));
    /// assert!(range.has(Ipv6Addr::from(0xA)));
    ///
    /// assert!(!range.has(Ipv6Addr::from(0xFFFF)));
    /// ```
    pub fn has (&self, ip: Ipv6Addr) -> bool {
        let needle = u128::from(ip);
        let start = u128::from(self.start());
        let end = u128::from(self.end());
        if start < end {
            needle >= start && needle <= end
        } else {
            needle >= end && needle <= start
        }
    }
}

impl fmt::Display for Ipv6AddrRange {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", &self.start, &self.end)
    }
}

impl From<(Ipv6Addr, Ipv6Addr)> for Ipv6AddrRange {
    /// Create an `Ipv6AddrRange` from a tuple of two `Ipv6Addr`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrRange;
    ///
    /// let start = Ipv6Addr::from(0x1);
    /// let end = Ipv6Addr::from(0xA);
    ///
    /// assert_eq!(Ipv6AddrRange::from((start, end)), Ipv6AddrRange::new(start, end));
    /// ```
    fn from (ips: (Ipv6Addr, Ipv6Addr)) -> Ipv6AddrRange {
        Ipv6AddrRange::new(ips.0, ips.1)
    }
}

impl FromStr for Ipv6AddrRange {
    type Err = NetAddsError;

    /// Parse a string as `Ipv6AddrRange`.
    ///
    /// If the string representation is not valid return an `NetAddsError::RangeAddrParse(RangeAddrParseError)`.
    ///
    /// Examples:
    ///
    /// ```
    /// use std::net::Ipv6Addr;
    ///
    /// use net_adds::Ipv6AddrRange;
    ///
    /// let a = Ipv6Addr::new(0xFFFF, 0, 0, 0, 0, 0, 0, 0xFF);
    /// let b = Ipv6Addr::new(0xFFFF, 0, 0, 0, 0, 0, 0, 0xFFFF);
    ///
    /// assert_eq!("ffff::ff-ffff::ffff".parse(), Ok(Ipv6AddrRange::new(a, b)));
    /// assert_eq!("ffff:0::ff-ffff::ffff".parse(), Ok(Ipv6AddrRange::new(a, b)));
    /// ```
    fn from_str (s: &str) -> Result<Self, Self::Err> {
        let mut ips = s.split('-').map(|ip| {
            Ipv6Addr::from_str(ip)
                .map_err(|_| NetAddsError::RangeAddrParse(RangeAddrParseError()))
        });

        let a = ips.next();
        let b = ips.next();

        if a.is_none() || b.is_none() || ips.next().is_some() {
            Err(NetAddsError::RangeAddrParse(RangeAddrParseError()))
        } else {
            Ok(Ipv6AddrRange::new(a.unwrap()?, b.unwrap()?))
        }
    }
}

#[cfg(test)]
mod test {
    use std::net::Ipv6Addr;

    use crate::NetAddsError;
    use crate::{Ipv6AddrRange, RangeAddrParseError};

    #[test]
    fn from_str () {
        let a = Ipv6Addr::from(0x1);
        let b = Ipv6Addr::from(0xA);
        let range = Ipv6AddrRange::new(a, b);
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
