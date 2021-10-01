pub mod errors;
pub use errors::*;

mod range;
pub use range::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};

mod network;
pub use network::{IpAddrNetwork, Ipv4AddrNetwork, Ipv6AddrNetwork};

mod iter;
pub use iter::{
    IntoSmartIterator,
    IpAddrSmartIterator,
    Ipv4AddrSmartIterator,
    Ipv6AddrSmartIterator,
    PortSmartIterator,
    SocketAddrIterator,
    SocketAddrSmartIterator
};

#[cfg(doctest)]
mod test {
    mod readme {
        macro_rules! external_doc_test {
            ($x:expr) => {
                #[doc = $x]
                extern {}
            };
        }

        external_doc_test!(include_str!("../README.md"));
    }
}
