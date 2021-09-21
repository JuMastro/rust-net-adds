use std::slice;
use std::net::{IpAddr, SocketAddr};

use crate::iter::PortSmartIterator;

/// A socket addr iterator.
///
/// This iterator stores all the values in memory, so it's recommended to use a `SocketAddrSmartIterator` for long series.
///
/// # Examples
///
/// ```
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
///
/// use net_adds::SocketAddrIterator;
///
/// let ips = &[Ipv4Addr::from(0)];
/// let mut iter = SocketAddrIterator::new(ips, &[0]);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 0)));
/// assert_eq!(iter.next(), None);
///
/// let ips = &[Ipv6Addr::from(0), Ipv6Addr::from(1)];
/// let mut iter = SocketAddrIterator::new(ips, &[0]);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 0)));
/// assert_eq!(iter.next(), None);
///
/// let ips = &[Ipv4Addr::from(0)];
/// let mut iter = SocketAddrIterator::new(ips, &[0, 1]);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 1)));
/// assert_eq!(iter.next(), None);
///
/// let ips = &[Ipv6Addr::from(0), Ipv6Addr::from(1)];
/// let mut iter = SocketAddrIterator::new(ips, &[0, 1]);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 1)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 1)));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct SocketAddrIterator<'a, Ip> {
    ip_iter: slice::Iter<'a, Ip>,
    ip_curr: Ip,
    port_iter: slice::Iter<'a, u16>,
    port_iter_initial: slice::Iter<'a, u16>
}

impl<'a, Ip: Copy> SocketAddrIterator<'a, Ip> {
    /// Returns a `SocketAddrIterator<'a, Ip>`.
    pub fn new (ips: &'a [Ip], ports: &'a [u16]) -> SocketAddrIterator<'a, Ip> {
        let mut ip_iter = ips.iter();
        let ip_curr = *ip_iter.next().unwrap();
        let port_iter = ports.iter();
        let port_iter_initial = port_iter.clone();
        SocketAddrIterator { ip_iter, ip_curr, port_iter, port_iter_initial }
    }
}

impl<'a, I> Iterator for SocketAddrIterator<'a, I>
where
    I: Copy,
    IpAddr: From<I>
{
    type Item = SocketAddr;

    fn next (&mut self) -> Option<Self::Item> {
        if let Some(port) = self.port_iter.next() {
            Some(SocketAddr::new(IpAddr::from(self.ip_curr), *port))
        } else {
            self.port_iter = self.port_iter_initial.clone();
            self.ip_curr = *self.ip_iter.next()?;
            Some(SocketAddr::new(IpAddr::from(self.ip_curr), *self.port_iter.next()?))
        }
    }
}

/// A smart socket addr iterator.
///
/// A smart iterator is an iterator that doesn't store all the items in memory. It's usefull for long series.
///
/// # Examples
///
/// ```
/// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
///
/// use net_adds::{IpAddrSmartIterator, Ipv4AddrSmartIterator, Ipv6AddrSmartIterator, SocketAddrSmartIterator};
///
/// let mut iter = SocketAddrSmartIterator::<Ipv4AddrSmartIterator, _>::new(Ipv4Addr::from(0), Ipv4Addr::from(0), 0, 0);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 0)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = SocketAddrSmartIterator::<Ipv6AddrSmartIterator, _>::new(Ipv6Addr::from(0), Ipv6Addr::from(1), 0, 0);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 0)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = SocketAddrSmartIterator::<IpAddrSmartIterator, _>::new(IpAddr::V4(Ipv4Addr::from(0)), IpAddr::V4(Ipv4Addr::from(0)), 0, 1);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 1)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = SocketAddrSmartIterator::<Ipv4AddrSmartIterator, _>::new(Ipv4Addr::from(0), Ipv4Addr::from(0), 0, 1);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::from(0)), 1)));
/// assert_eq!(iter.next(), None);
///
/// let mut iter = SocketAddrSmartIterator::<Ipv6AddrSmartIterator, _>::new(Ipv6Addr::from(0), Ipv6Addr::from(1), 0, 1);
///
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(0)), 1)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 0)));
/// assert_eq!(iter.next(), Some(SocketAddr::new(IpAddr::V6(Ipv6Addr::from(1)), 1)));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Clone, Debug)]
pub struct SocketAddrSmartIterator<It, Ip> {
    ip_iter: It,
    ip_curr: Ip,
    port_iter: PortSmartIterator,
    port_iter_initial: PortSmartIterator
}

impl<It, Ip> SocketAddrSmartIterator<It, Ip>
where
    It: Iterator<Item=Ip> + From<(Ip, Ip)>
{
    /// Returns a `SocketAddrSmartIterator<It, Ip>`.
    pub fn new (ip_start: Ip, ip_end: Ip, port_start: u16, port_end: u16) -> SocketAddrSmartIterator<It, Ip> {
        let mut ip_iter = It::from((ip_start, ip_end));
        let ip_curr = ip_iter.next().unwrap();
        let port_iter = PortSmartIterator::new(port_start, port_end);
        let port_iter_initial = port_iter.clone();
        SocketAddrSmartIterator { ip_iter, ip_curr, port_iter, port_iter_initial }
    }
}

impl<It, Ip> Iterator for SocketAddrSmartIterator<It, Ip>
where
    It: Iterator<Item=Ip>,
    Ip: Copy,
    IpAddr: From<Ip>
{
    type Item = SocketAddr;

    fn next (&mut self) -> Option<Self::Item> {
        if let Some(port) = self.port_iter.next() {
            Some(SocketAddr::new(IpAddr::from(self.ip_curr), port))
        } else {
            self.port_iter = self.port_iter_initial.clone();
            self.ip_curr = self.ip_iter.next()?;
            Some(SocketAddr::new(IpAddr::from(self.ip_curr), self.port_iter.next()?))
        }
    }
}
