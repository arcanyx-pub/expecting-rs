# Expecting

[![Crates.io](https://img.shields.io/crates/v/expecting)](https://crates.io/crates/expecting)
[![Documentation](https://docs.rs/expecting/badge.svg)](https://docs.rs/expecting)
[![Crates.io](https://img.shields.io/crates/l/expecting)](LICENSE)

**Expecting** provides macros for testing conditions without panicking. The
`expect_*` family of macros cause an early return of [`anyhow::Error`] if the
expected condition is not met.

This crate is especially helpful in async integration tests that involve
provisioning and tearing down resources; rather than struggle to catch panics,
you can simply use `expect_*` instead of `assert_*` to return [`Result`].

See [the docs](https://docs.rs/expecting) for usage examples and more info.
