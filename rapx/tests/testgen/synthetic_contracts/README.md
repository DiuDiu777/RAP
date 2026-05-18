# Synthetic Contract Benchmarks

This directory contains small Rust crates for contract-guided test generation.
Each crate exposes a safe public API that internally calls one or more unsafe
standard-library APIs. The crates are intentionally tiny so that RAP testgen can
be run on each crate independently and report contract coverage.

The current suite covers five primitive SP families from `primitive-sp.md` with
three crates per family:

- `Layout`: alignment, layout validity, size/offset assumptions.
- `Pointer`: non-null, in-bound, dangling/valid pointer assumptions.
- `Content`: UTF-8, C string, unwrap/initialization assumptions.
- `AliasLifetime`: ownership, aliasing, lifetime/owned-pointer assumptions.
- `Misc`: unreachable, pinning, volatile-style hazards.

Run a crate with the normal testgen flow from inside that crate directory, for
example:

```sh
cd tests/testgen/synthetic_contracts/content_utf8_public
cargo rapx -testgen
```

