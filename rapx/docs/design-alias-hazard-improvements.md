# RAPx Alias Hazard Verification Improvements — Design Plan

## 1. Problem Statement

`cargo rapx verify` on `tests/verify_cases/std-challenge-18` reports 3 UNSOUND functions,
all alias-hazard false positives:

| Function | Checkpoint | Fails |
|----------|-----------|-------|
| `RChunksMut::get_unchecked` | `from_raw_parts_mut` | `[hazard] Alias` |
| `ArrayWindows::next` | `raw-ptr-deref` (`&*`) | `[hazard] Alias` |
| `ArrayWindows::next_back` | `raw-ptr-deref` (`&*`) | `[hazard] Alias` |

All are structurally safe:
- `RChunksMut::get_unchecked` creates `&'a mut [T]` from a raw `*mut [T]` field
  the struct exclusively owns.
- `ArrayWindows::next`/`next_back` create `&'a [T; N]` (shared ref) from
  `self.v.as_ptr()` where `self.v: &'a [T]` is a shared reference.

The root cause is the **forward-state origin-resolution chain** breaking for
three distinct reasons, described below.

---

## 2. Root-Cause Analysis

### 2.A — `RChunksMut::get_unchecked`: struct-field provenance lost across complex BBs

```
self.v.as_mut_ptr().add(start)                  →  from_raw_parts_mut(ptr, len)
^^^^^^^^^^^^^^^^^^^^^^^^^^^
resolved origin                                          ↑ checkpoint
```

The `check()` function at `alias.rs:135` successfully runs `local_hazard_violation`
(no conflict) and `destination_flows_to_return` (escapes).  It then calls
`self_field_origin()` at line 270, which **requires the origin to be**
`PlaceKey { base: Local(1), fields: [v_field_index] }`.

The forward-state resolution chain is:

```
_4 ← add(_3, start)           ←  resolve_forward_place: follows PointsTo → _3
_3 ← as_mut_ptr(_2)            ←  resolve_forward_place: follows PointsTo → _2
_2 ← Move((_1.0))              ←  resolve_forward_place: AbstractValue::Place → _1.0
_1 ← self                      ←  no entry in forward.values; stop
  → origin = PlaceKey { base: Local(1), fields: [0] }   ✓  correct
```

**Why this sometimes fails**: the intermediate local `_2` is produced by
`Move(_1.0)` or similar field projection.  The forward verifier records
`_2 → AbstractValue::Place(PlaceKey { base: 1, fields: [0] })` only when the
`Assign` statement is included in the sliced MIR path.  For paths with
additional basic blocks (e.g., `saturating_sub` introducing an extra BB),
the backward slicer may exclude the `_2 = (_1.0)` assignment, or the
forward value-map may be rebuilt from a different entry-point, losing the
mapping.

**Counter-example that works**: `ChunksMut::get_unchecked` uses
`from_raw_parts_mut(self.v.as_mut_ptr().add(start), len)` with
`start = idx * self.chunk_size` — a simpler MIR that produces fewer BBs.
The slicer correctly includes the field-load, and the forward value-map
retains `_2 → Place(_1.0)`.

---

### 2.B — `ArrayWindows::next` / `next_back`: `as_ptr()` chain not resolved through `&[T]`

```
self.v.as_ptr() as *const [T; N]  →  &* (... )      ← raw-ptr-deref checkpoint
^^^^^^^^^^^^^^^
```

`check()` dispatches to `check_raw_ptr_deref_alias()` (line 141-142).  That
function:

1. `local_hazard_violation` — finds nothing ✓
2. `destination_flows_to_return` — true (escapes in `Some(ret)`)
3. `self_field_origin` — fails because `ArrayWindows.v` is `&'a [T]` (not a raw
   pointer), so the escaped-field check short-circuits
4. `resolve_param_origin` — returns `Local(1)` (self), type is
   `&mut ArrayWindows`, not the underlying `&[T]`
5. `alias_proved_for_param_local(Local(1), SharedView)` — sees `&mut` →
   returns `proved` … **but this should be reached and shouldn't fail**.

**The actual failure**: `alias_proved_for_param_local` checks `_1`'s type
(`&mut ArrayWindows`) and returns `proved` for `SharedView`.  So this should
actually pass.  The fact that it **fails** implies `resolve_param_origin`
does **not** return `Some(1)`, meaning the `origin` resolved from the
raw-ptr-deref operand does **not** have `base = Local(1)`.

Likely: the `as_ptr()` call on `<[T]>::as_ptr` is recognized by
`is_as_ptr()`, and `eff_alias_ptr` produces a `ReturnPointerFromArg { arg: 0 }`
effect that creates `PointsTo { pointer: _cast, source: _self_ptr }`.
However, for `self.v.as_ptr()` where `self.v` is obtained through
`&(*_1).v`, the `operand_place` of the call's arg-0 may return
`PlaceKey { base: Local(_temp), fields: [] }` where `_temp` is the
field-read temporary, not `_1.v` directly.

Additionally, after the `as *const [T; N]` cast, `resolve_forward_place`
handles `AbstractValue::Cast` (line 1018-1023) but then `place` becomes the
inner value.  If the inner value is itself a `CallResult` from `as_ptr()`,
the resolution continues.  However, if the cast's inner value is
`Unknown` or `Place` of an intermediate local that was sliced out, the
chain stops.

---

### 2.C — Combined effect

In both patterns, the forward-state chain that should connect the checkpoint
operand back to `_1.0` (the struct field) is **fragile**: it depends on
every intermediate MIR statement being included in the backward slice and
having a correct abstract value recorded in the forward visit.

---

## 3. Proposed Improvements

### I.  `trace_raw_ptr_through_call` — extend to cover `as_ptr`/`as_mut_ptr`

*File*: `src/verify/smt_check/alias.rs`, function `trace_raw_ptr_through_call`
(line 426–484)

Currently only handles `get_unchecked` / `get_unchecked_mut`.  Extend to:

```
callee.contains("::as_ptr") && !callee.contains("::as_ptr_range")
callee.contains("::as_mut_ptr") && !callee.contains("::as_mut_ptr_range")
```

When a raw ptr deref's operand is defined by such a call, the call's
receiver (`args[0]`) is the **slice reference** or **raw slice pointer**
that owns the memory.  Return that place so the caller can apply
`alias_proved_for_param_local` on it.

**Effect**: `ArrayWindows::next` / `next_back` would trace through
`self.v.as_ptr()` and find that the underlying origin is `self.v: &'a [T]`
(a shared reference).  For `SharedView`, this is automatically proved.

---

### II.  Propagate struct-field origin through `as_mut_ptr()` on `*mut [T]`

*File*: `src/verify/call_summary/fn_simulator.rs`

Current: `E!(is_as_ptr, dep0!(), false, none!(), eff_alias_ptr)` handles
`as_ptr`/`as_mut_ptr` with `ReturnPointerFromArg { arg: 0 }`, which creates:

```
PointsTo { pointer: _result, source: _receiver }
```

Problem: when the receiver is an intermediate temporary (`_2`) that was
produced by `_2 = Copy((*_1).0)`, the forward state has
`_2 → AbstractValue::Place(_1.0)`.  This **should** chain correctly in
`resolve_forward_place`.  But the sliced-MIR fact is that `_2`'s abstract
value may not be recorded if the field-load assignment was sliced out.

**Fix — option A (slicer-aware)**: In `build_raw_ptr_deref_checks`
(`target.rs:1222`), when a raw-ptr-deref originates from an `as_ptr`-like
call, add the receiver's definition to the sliced set as a side-input.
This ensures the field-load is always included.

**Fix — option B (forward-state)**: In the forward verifier, when processing
an `as_mut_ptr`/`as_ptr` call that has a single predecessor (unique
definition), eagerly resolve the receiver through `ABSTRACT_VALUE`:

```
if forward.values contains `receiver → Place(field_path)`
  → emit PointsTo { pointer: result, source: field_path }
  instead of Pointer { pointer: result, source: receiver }
```

Option B is more targeted and less invasive.

---

### III.  `check_raw_ptr_deref_alias` — field-type-aware shared view check

*File*: `src/verify/smt_check/alias.rs`, function `check_raw_ptr_deref_alias`
(line 511–626)

After `resolve_param_origin` returns `Some(local_index)`:

```rust
let param_origin = resolve_param_origin(checker.tcx, checkpoint.caller, &origin);
if let Some(local_index) = param_origin {
    // NEW: also check if the *origin* has fields and the innermost field
    //      is a shared reference — shared views are always safe.
    if !origin.fields.is_empty() {
        let field_ty = field_type_at_origin(checker.tcx, checkpoint.caller, &origin);
        if is_shared_reference(field_ty) {
            return SmtCheckResult::proved(
                "shared view through a struct field that holds a shared reference",
            );
        }
    }
    if let Some(result) =
        alias_proved_for_param_local(checker.tcx, checkpoint.caller, local_index, kind)
    {
        return result;
    }
}
```

**Effect**: When `self` is `&mut ArrayWindows` but `self.v` is `&'a [T]`
(shared ref), the field-type check would prove the shared view safe
without requiring the full origin chain to be intact.

---

### IV.  Improve `from_raw_parts_mut` field-origin detection robustness

*File*: `src/verify/smt_check/alias.rs`, function `check` (line 135–343)

After `self_field_origin` fails, add a fallback that checks whether
`destination` flows through a field whose type is a raw pointer inside a
struct the function owns:

```rust
// Current (line 338-342):
let err_msg = format!(
    "returned view escapes while the original pointer is not owned by a private self field [origin={:?}]",
    origin
);
failed_smt(err_msg)

// Proposed: before the error, try a field-aware origin resolution.
// Walk `origin` backwards through the collected PointsTo facts to see
// if it ultimately targets a struct-field raw pointer.
if let Some(sfo) = resolve_origin_to_self_field(checker, checkpoint, forward, &origin) {
    if escaped_self_field_violation(...).is_none() {
        return SmtCheckResult::proved(...);
    }
}
```

Where `resolve_origin_to_self_field` walks the full PointsTo chain (not
just the `resolve_forward_place` chain) to find the ultimate struct-field
source.  The difference is: instead of relying solely on
`forward.values.get(&local)`, also search `forward.facts` for additional
`PointsTo` edges that may exist but aren't chained through
`AbstractValue::Place`.

---

### V.  Summary of changes

| # | Where | What | Effort | Blocks which FP |
|---|-------|------|--------|-----------------|
| I | `alias.rs:426` | Extend `trace_raw_ptr_through_call` to `as_ptr` | Small | ArrayWindows (2,3) |
| II | `fn_simulator.rs` / `verifier.rs` | Eager origin resolution for `as_mut_ptr` | Medium | RChunksMut (1) |
| III | `alias.rs:568` | Field-type-aware shared view check | Small | ArrayWindows (2,3) |
| IV | `alias.rs:338` | Fallback PointsTo-chain walk for field-origin | Medium | RChunksMut (1) |

All four are independent and can be implemented incrementally.
I and III are the most impactful for the immediate false positives.

---

## 4. Verification Plan

After implementing each improvement:

```bash
# Run the failing test case
cd tests/verify_cases/std-challenge-18 && cargo rapx verify

# Run the full verify test suite
cargo test -p rapx -- verify_units verify_cases

# Check no regressions on alias sound/unsound cases
cargo test -p rapx -- verify_hazard
```

Expected outcome: all 3 UNSOUND → SOUND, no new regressions on existing
alias sound/unsound tests.
