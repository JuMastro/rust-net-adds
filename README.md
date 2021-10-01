# net-adds
Provides IP ranges, networks and iterators for Rust.

### Documentation

Read documentation [here](https://jumastro.github.io/rust-net-adds).

### Install
```toml
[dependencies]
net-adds = { git = "https://github.com/JuMastro/rust-net-adds", version = "0.1.0" }
```

### Examples
> All examples also works with IPv6. Read the documentation for more examples.
```rust
use net_adds::{
    Ipv4Addr,
    Ipv4AddrRange,
    Ipv4AddrNetwork,
    IntoSmartIterator,
    Ipv4AddrSmartIterator,
    SocketAddrIterator,
    SocketAddrSmartIterator
};

let range = Ipv4AddrRange::new(Ipv4Addr::new(192, 168, 0, 0), Ipv4Addr::new(192, 168, 0, 255));
assert_eq!(Ok(range), "192.168.0.0-192.168.0.255".parse());

let network = Ipv4AddrNetwork::try_new(Ipv4Addr::new(192, 168, 0, 22), 24).unwrap();
assert_eq!(Ok(network), "192.168.0.22/24".parse());
assert_eq!(Ok(network), "192.168.0.22/255.255.255.0".parse());

// The range must match with the network.
assert!(
    range.into_iter()
        .zip(network.into_smart_iter())
        .any(|(r, n)| r == n)
);

// Socket addr iterator.
let ips = &[Ipv4Addr::new(192, 168, 0, 0), Ipv4Addr::new(192, 168, 0, 2)];
let ports = &[8000, 8002];
let mut iter = SocketAddrIterator::new(ips, ports);

assert_eq!(iter.next(), "192.168.0.0:8000".parse().ok());
assert_eq!(iter.next(), "192.168.0.0:8002".parse().ok());
assert_eq!(iter.next(), "192.168.0.2:8000".parse().ok());
assert_eq!(iter.next(), "192.168.0.2:8002".parse().ok());
assert_eq!(iter.next(), None);

// Socket addr smart iterator.
let mut iter = SocketAddrSmartIterator::<Ipv4AddrSmartIterator, _>::new(
    Ipv4Addr::new(192, 168, 0, 0),
    Ipv4Addr::new(192, 168, 0, 2),
    8000,
    8002
);

assert_eq!(iter.next(), "192.168.0.0:8000".parse().ok());
assert_eq!(iter.next(), "192.168.0.0:8001".parse().ok());
assert_eq!(iter.next(), "192.168.0.0:8002".parse().ok());
assert_eq!(iter.next(), "192.168.0.1:8000".parse().ok());
assert_eq!(iter.next(), "192.168.0.1:8001".parse().ok());
assert_eq!(iter.next(), "192.168.0.1:8002".parse().ok());
assert_eq!(iter.next(), "192.168.0.2:8000".parse().ok());
assert_eq!(iter.next(), "192.168.0.2:8001".parse().ok());
assert_eq!(iter.next(), "192.168.0.2:8002".parse().ok());
assert_eq!(iter.next(), None);
```
