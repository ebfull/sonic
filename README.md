# Sonic

This crate is an implementation of **Sonic**, a protocol for quickly verifiable, compact zero-knowledge proofs of arbitrary computations. Sonic is intended to be an alternative to zk-SNARKs which typically require a trusted setup for each individual computation. Sonic is _universal_ in that it requires a single setup, and _updateable_ in that the parameters can be continually strengthened. In exchange, Sonic proofs are slightly longer and slightly slower to verify in practice.

**THIS IMPLEMENTATION IS A PROTOTYPE AND IS FULL OF BUGS, DO NOT USE IT IN PRODUCTION**

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
