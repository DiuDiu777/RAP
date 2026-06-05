# Synthetic Contract Benchmarks

This directory contains small Rust crates for contract-guided test generation.
Each crate exposes only safe public APIs while internally relying on unsafe
standard-library operations. The suite is organized by trigger mechanism, not
only by primitive safety-property family. This keeps a small number of public
field baselines while adding cases that require method mutation, ordered state
propagation, constructor flow, resource recipes, generic choices, transformed
inputs, and post-call hazards.

Representative trigger classes:

- `public-field baseline`: direct external mutation, kept mainly as a sanity
  check for CGAG field edges.
- `method-only mutation`: the relevant field is private and can only be updated
  through a safe method parameter.
- `ordered propagation`: one method writes an intermediate field and a later
  method transfers it into the contract-sensitive field.
- `derived state`: the target field cannot be set directly; it is computed from
  multiple public inputs.
- `generic alignment`: the violation depends on selecting a high-alignment
  monomorphization such as `u128`.
- `resource recipe`: the bad value requires multiple safe statements, such as
  constructing a dangling raw pointer.
- `post-call hazard`: an unsafe call creates a reference/alias obligation, and a
  later safe method invalidates it.

Run a crate with the normal testgen flow from inside that crate directory, for
example:

```sh
cd tests/testgen/synthetic_contracts/content_utf8_public
cargo rapx -testgen
```

`manifest.json` records the intended family, unsafe API, trigger class, and
mutator source for each crate. Some crates intentionally exceed the current
prototype's generation ability; they are included to define the target coverage
of the CGAG design and to drive future testgen development.
