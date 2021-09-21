### 0.1.0

> Created at 21/09/2021

  - Add error enum (`NetAddsError`) which can be `RangeAddrParseError`,
    `NetworkAddrParseError`, `InvalidNetmaskError` or `InvalidNetmaskPrefixError`.
  - Add `IpAddrRange`, `Ipv4AddrRange` and `Ipv6AddrRange`.
  - Add `IpAddrNetwork`, `Ipv4AddrNetwork` and `Ipv6AddrNetwork`.
  - Add `PortSmartIterator`.
  - Add `SocketAddrIterator` and `SocketAddrSmartIterator`.
  - Implements iterators for ranges and networks.
