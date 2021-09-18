pub use crate::range::RangeAddrParseError;
pub use crate::network::{NetworkAddrParseError, InvalidNetmaskError, InvalidNetmaskPrefixError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetAddsError {
    RangeAddrParse(RangeAddrParseError),
    NetworkAddrParse(NetworkAddrParseError),
    InvalidNetmask(InvalidNetmaskError),
    InvalidNetmaskPrefix(InvalidNetmaskPrefixError)
}
