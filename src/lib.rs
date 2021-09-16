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
