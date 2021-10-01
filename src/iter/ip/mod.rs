use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

pub mod v4;
use v4::*;

pub mod v6;
use v6::*;

/// An IP address smart iterator, either IPv4 or IPv6.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
///
/// ```
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
///
/// use net_adds::{IpAddrSmartIterator, Ipv4AddrSmartIterator, Ipv6AddrSmartIterator};
///
/// let mut iter = IpAddrSmartIterator::V4(Ipv4AddrSmartIterator::new(Ipv4Addr::from(0), Ipv4Addr::from(1)));
///
/// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0))));
/// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 1))));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = IpAddrSmartIterator::V6(Ipv6AddrSmartIterator::new(Ipv6Addr::from(0), Ipv6Addr::from(1)));
///
/// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0))));
/// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1))));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub enum IpAddrSmartIterator {
    V4(Ipv4AddrSmartIterator),
    V6(Ipv6AddrSmartIterator)
}

impl IpAddrSmartIterator {
    /// Returns true if the iterator is an IPv4 iterator, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrSmartIterator, Ipv4AddrSmartIterator, Ipv6AddrSmartIterator};
    ///
    /// let start = Ipv4Addr::new(0, 0, 0, 0);
    /// let end = Ipv4Addr::new(0, 0, 0, 2);
    /// assert_eq!(IpAddrSmartIterator::V4(Ipv4AddrSmartIterator::new(start, end)).is_ipv4(), true);
    ///
    /// let start = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let end = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2);
    /// assert_eq!(IpAddrSmartIterator::V6(Ipv6AddrSmartIterator::new(start, end)).is_ipv4(), false);
    /// ```
    pub fn is_ipv4 (&self) -> bool {
        match self {
            IpAddrSmartIterator::V4(_) => true,
            IpAddrSmartIterator::V6(_) => false
        }
    }

    /// Returns true if the iterator is an IPv6 iterator, else return false.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrSmartIterator, Ipv4AddrSmartIterator, Ipv6AddrSmartIterator};
    ///
    /// let start = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    /// let end = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2);
    /// assert_eq!(IpAddrSmartIterator::V6(Ipv6AddrSmartIterator::new(start, end)).is_ipv6(), true);
    ///
    /// let start = Ipv4Addr::new(0, 0, 0, 0);
    /// let end = Ipv4Addr::new(0, 0, 0, 2);
    /// assert_eq!(IpAddrSmartIterator::V4(Ipv4AddrSmartIterator::new(start, end)).is_ipv6(), false);
    /// ```
    pub fn is_ipv6 (&self) -> bool {
        match self {
            IpAddrSmartIterator::V4(_) => false,
            IpAddrSmartIterator::V6(_) => true
        }
    }
}

impl Iterator for IpAddrSmartIterator {
    type Item = IpAddr;

    fn next (&mut self) -> Option<Self::Item> {
        match self {
            IpAddrSmartIterator::V4(iter) => Some(IpAddr::V4(iter.next()?)),
            IpAddrSmartIterator::V6(iter) => Some(IpAddr::V6(iter.next()?))
        }
    }
}

impl fmt::Display for IpAddrSmartIterator {
    fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpAddrSmartIterator::V4(iter) => write!(f, "V4({})", iter),
            IpAddrSmartIterator::V6(iter) => write!(f, "V6({})", iter)
        }
    }
}

impl From<Ipv4AddrSmartIterator> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator::V4` from an `Ipv4AddrSmartIterator`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr};
    ///
    /// use net_adds::{IpAddrSmartIterator, Ipv4AddrSmartIterator};
    ///
    /// let mut iter = IpAddrSmartIterator::from(Ipv4AddrSmartIterator::new(Ipv4Addr::from(0), Ipv4Addr::from(1)));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (iter: Ipv4AddrSmartIterator) -> IpAddrSmartIterator {
        IpAddrSmartIterator::V4(iter)
    }
}

impl From<Ipv6AddrSmartIterator> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator::V6` from an `Ipv6AddrSmartIterator`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// use net_adds::{IpAddrSmartIterator, Ipv6AddrSmartIterator};
    ///
    /// let mut iter = IpAddrSmartIterator::from(Ipv6AddrSmartIterator::new(Ipv6Addr::from(0), Ipv6Addr::from(1)));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (iter: Ipv6AddrSmartIterator) -> IpAddrSmartIterator {
        IpAddrSmartIterator::V6(iter)
    }
}

impl From<(IpAddr, IpAddr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` V4 or V6 from a tuple `(IpAddr, IpAddr)`.
    ///
    /// Panic if IPv4 and IPv6 are mixed.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// use net_adds::IpAddrSmartIterator;
    ///
    /// let mut iter = IpAddrSmartIterator::from((IpAddr::V4(Ipv4Addr::from(0)), IpAddr::V4(Ipv4Addr::from(1))));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = IpAddrSmartIterator::from((IpAddr::V6(Ipv6Addr::from(0)), IpAddr::V6(Ipv6Addr::from(1))));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (ips: (IpAddr, IpAddr)) -> IpAddrSmartIterator {
        match ips {
            (IpAddr::V4(a), IpAddr::V4(b)) => {
                IpAddrSmartIterator::V4(Ipv4AddrSmartIterator::new(a, b))
            },
            (IpAddr::V6(a), IpAddr::V6(b)) => {
                IpAddrSmartIterator::V6(Ipv6AddrSmartIterator::new(a, b))
            },
            _ => {
                panic!("cannot mix IPv4 and IPv6 to build a range ip")
            }
        }
    }
}

impl From<(Ipv4Addr, Ipv4Addr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` from a tuple `(Ipv4Addr, Ipv4Addr)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr};
    ///
    /// use net_adds::IpAddrSmartIterator;
    ///
    /// let mut iter = IpAddrSmartIterator::from((Ipv4Addr::from(0), Ipv4Addr::from(1)));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V4(Ipv4Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (ips: (Ipv4Addr, Ipv4Addr)) -> IpAddrSmartIterator {
        IpAddrSmartIterator::V4(Ipv4AddrSmartIterator::new(ips.0, ips.1))
    }
}


impl From<(Ipv6Addr, Ipv6Addr)> for IpAddrSmartIterator {
    /// Create an `IpAddrSmartIterator` from a tuple `(Ipv6Addr, Ipv6Addr)`.
    ///
    /// # Examples:
    ///
    /// ```
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// use net_adds::IpAddrSmartIterator;
    ///
    /// let mut iter = IpAddrSmartIterator::from((Ipv6Addr::from(0), Ipv6Addr::from(1)));
    ///
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(0))));
    /// assert_eq!(iter.next(), Some(IpAddr::V6(Ipv6Addr::from(1))));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn from (ips: (Ipv6Addr, Ipv6Addr)) -> IpAddrSmartIterator {
        IpAddrSmartIterator::V6(Ipv6AddrSmartIterator::new(ips.0, ips.1))
    }
}
