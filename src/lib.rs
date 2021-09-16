// Re-export std addr to allow single line `use`.
pub use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

pub mod errors;
pub use errors::*;

mod range;
pub use range::{IpAddrRange, Ipv4AddrRange, Ipv6AddrRange};

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
