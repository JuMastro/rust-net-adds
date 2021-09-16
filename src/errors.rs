pub use crate::range::RangeAddrParseError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetAddsError {
    RangeAddrParse(RangeAddrParseError)
}
