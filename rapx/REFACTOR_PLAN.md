# Verify Module Refactoring Plan

## Goal

Replace the current "pattern-matching → StateFact extraction → per-property SMT dispatch"
pipeline with a **symbolic MIR virtual machine** that executes retained MIR items and
produces a symbolic state directly consumable by a single unified property checker.

---

## 1. Target Architecture

```
PathExtractor (keep)          BackwardSlicer (keep)
      │                              │
      │  PathTree                    │  RelevantMirItems
      │                              │
      └──────────┬───────────────────┘
                 ▼
         VerifyEngine (refactored)
                 │
    ┌────────────┼────────────┐
    │            ▼            │
    │    Symbolic MIR VM      │  ← NEW: replaces ForwardVerifier + SmtModel
    │    (stateful executor)  │
    │            │            │
    │            ▼            │
    │     VmState             │  symbolic locals + memory + path conditions
    │            │            │
    │            ▼            │
    │  UnifiedPropertyChecker │  ← NEW: replaces 20 smt_check/*.rs
    │            │            │
    │            ▼            │
    │       CheckResult       │
    └─────────────────────────┘
```

**Key difference from current:**
- Current: `ForwardVerifier` pattern-matches MIR → emits ad-hoc `StateFact`s →
  each `smt_check/*.rs` manually scavenges facts → builds Z3 terms → checks
- Target: VM executes MIR → VmState holds Z3 terms natively →
  property checker asserts constraints on VmState → Z3 solves once

---

## 2. New Module Design

### 2.1 `src/verify/vm/` — Symbolic MIR Virtual Machine

```
src/verify/vm/
├── mod.rs          # SymbolicVm struct, public API
├── state.rs        # VmState, VmValue, MemoryModel
├── exec.rs         # MIR statement/terminator executors
├── memory.rs       # Symbolic heap/stack allocation model
├── call.rs         # Call handling (summaries + interprocedural)
└── display.rs      # Debug/diagnostic formatting
```

#### 2.1.1 `state.rs` — Core State Types

```rust
/// A symbolic value tracked during VM execution.
pub struct VmValue<'ctx> {
    /// The Z3 integer term representing this value (address or scalar).
    pub term: Int<'ctx>,

    /// Rust type, for layout queries (size, align).
    pub ty: Ty<'tcx>,

    /// Allocation metadata: if this value is a pointer, which allocation
    /// object does it point into?  (base, size_in_bytes).
    pub provenance: Option<AllocId>,

    /// Constraints already known about this value (non-null, aligned, etc.).
    /// These are already asserted in the solver during execution.
    pub invariants: ValueInvariants,
}

bitflags! {
    pub struct ValueInvariants: u8 {
        const NON_NULL   = 1 << 0;
        const ALIGNED    = 1 << 1;
        const INIT       = 1 << 2;
        const IN_BOUNDS  = 1 << 3;
    }
}

/// A heap/stack allocation object.
pub struct Allocation<'ctx> {
    /// Unique identifier.
    pub id: AllocId,

    /// Base address (fresh Z3 constant).
    pub base: Int<'ctx>,

    /// Size in bytes (Z3 term, may be symbolic e.g. from len()).
    pub size: Int<'ctx>,

    /// Alignment in bytes.
    pub align: u64,

    /// Element type for bounds checking (None = raw bytes).
    pub element_ty: Option<Ty<'tcx>>,

    /// Symbolic memory content: Z3 Array from address offset to byte/int value.
    /// Lazily populated.  None means contents are uninitialized.
    pub contents: Option<z3::ast::Array<'ctx>>,
}

/// The full symbolic state at a program point.
pub struct VmState<'ctx, 'tcx> {
    /// Z3 context (shared across all terms).
    ctx: &'ctx z3::Context,

    /// Z3 solver with incremental assertions.
    solver: z3::Solver<'ctx>,

    /// MIR body being executed.
    body: &'a Body<'tcx>,

    /// Value bound to each MIR local at the current program point.
    locals: FxHashMap<Local, VmValue<'ctx>>,

    /// All known allocations (stack + heap).
    allocations: FxHashMap<AllocId, Allocation<'ctx>>,

    /// Active path conditions (SwitchInt/Assert branches taken).
    path_conditions: Vec<Bool<'ctx>>,

    /// Current program point (for cursor-based queries).
    cursor: ValueCursor,

    /// Per-place definition stack (for loop-carried value resolution).
    definitions: Vec<(PlaceKey, VmValue<'ctx>, ValueCursor)>,
}
```

#### 2.1.2 `exec.rs` — MIR Executors

One function per MIR statement/terminator kind — each is a pure transfer function
`VmState → VmState`:

```rust
impl VmState<'ctx, 'tcx> {
    fn exec_assign(&mut self, place: &Place, rvalue: &Rvalue);
    fn exec_call(&mut self, func: &Operand, args: &[Operand], dest: Place, ...);
    fn exec_switchint(&mut self, discr: &Operand, targets: &SwitchTargets);
    fn exec_assert(&mut self, cond: &Operand, expected: bool);
    fn exec_storage_live(&mut self, local: Local);
    fn exec_storage_dead(&mut self, local: Local);
    fn exec_drop(&mut self, place: &Place);
    // ...
}
```

**Key executors:**

| MIR Construct | VM Action |
|---|---|
| `Assign(dest, Use(op))` | `dest = op` — copy VmValue |
| `Assign(dest, Ref(place))` | Allocate `place`, set `dest` = base addr, mark NON_NULL + ALIGNED + INIT |
| `Assign(dest, RawPtr(place))` | Allocate `place`, set `dest` = base addr, less strict invariants |
| `Assign(dest, BinaryOp(op, (l,r)))` | Compute Z3 term: `z3_l op z3_r`, add constraint showing relationship |
| `Assign(dest, Cast(kind, op, ty))` | Reinterpret value with new type, preserve provenance |
| `Assign(dest, Len(place))` | Look up allocation size for the slice/array |
| `Assign(dest, Aggregate(kind, ops))` | Track field → element relationships |
| `Call(func, args, dest)` | Look up effect summary, apply VmState transform |
| `SwitchInt(discr, targets)` | Assert `discr == chosen_value` as path condition |
| `Assert(cond, expected)` | Assert `cond == expected` as path condition |
| `StorageLive(local)` | Optionally create stack allocation |
| `StorageDead(local)` | Mark allocation freed, add use-after-free guard |
| `Drop(place)` | Add drop constraint |

#### 2.1.3 `memory.rs` — Symbolic Memory

```rust
impl VmState<'ctx, 'tcx> {
    /// Allocate a new object on the heap or stack.  Returns its AllocId.
    fn allocate(&mut self, ty: Ty<'tcx>, size: Option<Int<'ctx>>) -> AllocId;

    /// Read a value from memory at a given pointer + offset.
    fn memory_read(&mut self, ptr: &VmValue, offset: Int<'ctx>, ty: Ty) -> VmValue;

    /// Write a value to memory at a given pointer + offset.
    fn memory_write(&mut self, ptr: &VmValue, offset: Int<'ctx>, value: &VmValue);

    /// Compute the address of a MIR place (symbolically).
    /// For stack locals: fresh constant per StorageLive.
    /// For projections: offset by field/index.
    fn address_of_place(&self, place: &Place) -> VmValue;
}
```

**Memory model choice:** Use a **flat byte-addressable model** with Z3 Array theory.
Each allocation is a separate Z3 Array `[base, base + size) → byte`.  Pointers carry
an `AllocId` for provenance tracking (which allocation they point into).

For the initial implementation, focus on pointer-level properties.  Memory content
modeling (reads/writes) can be added incrementally as needed for `Init` and
`NonOverlap` properties.

#### 2.1.4 `mod.rs` — Public API

```rust
pub struct SymbolicVm<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl SymbolicVm {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self;

    /// Execute retained MIR items in path order, producing a symbolic state.
    /// Returns None if execution encounters an unsupported MIR construct
    /// (with a diagnostic reason string).
    pub fn execute(
        &self,
        items: &RelevantMirItems<'tcx>,
    ) -> Result<VmState<'_, 'tcx>, UnsupportedReason>;
}
```

---

### 2.2 `src/verify/property_checker.rs` — Unified Property Checker

```rust
pub struct PropertyChecker;

impl PropertyChecker {
    /// Check a single property against a VM state.
    /// The VM state already has all path conditions asserted in its solver.
    /// This method adds the property's negation and checks satisfiability.
    pub fn check(
        vm_state: &mut VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult;
}
```

**Internal dispatch — a single `match property.kind`:**

```rust
fn check(vm_state, checkpoint, property) -> CheckResult {
    match property.kind {
        Align      => self.check_align(vm_state, property),
        NonNull    => self.check_non_null(vm_state, property),
        Allocated  => self.check_allocated(vm_state, property),
        InBound    => self.check_in_bound(vm_state, property),
        Init       => self.check_init(vm_state, property),
        Typed      => self.check_typed(vm_state, property),
        Alias      => self.check_alias(vm_state, property),
        Owning     => self.check_owning(vm_state, property),
        Alive      => self.check_alive(vm_state, property),
        NonOverlap => self.check_non_overlap(vm_state, property),
        ValidPtr   => self.check_valid_ptr(vm_state, property),
        // compound → decompose
        Deref      => self.check_decomposed(vm_state, property, &[Allocated, InBound]),
        Ptr2Ref    => self.check_decomposed(vm_state, property, &[Init, Align, Alias]),
        Layout     => self.check_decomposed(vm_state, property, &[Allocated]),
        // ...
    }
}
```

**Key difference from current:** Each `check_*` helper is a ~15-line function that:
1. Extracts the relevant VmValue(s) for the property's target place from `vm_state`
2. Builds the property-specific SMT assertion on those values
3. Pushes it (negated) to the solver
4. Calls `solver.check()` → `Proved` (unsat) / `Failed` (sat) / `Unknown`

No manual fact-scavenging, no separate SmtModel construction, no separate
`assert_forward_facts` step — the facts are already in the solver from VM execution.

---

### 2.3 Refactored `engine.rs`

```rust
pub struct VerifyEngine<'tcx> {
    slicer: BackwardSlicer<'tcx>,
    vm: SymbolicVm<'tcx>,
    checker: PropertyChecker,
}

impl VerifyEngine {
    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<CheckResult> {
        // 1. Backward slice → Vec<RelevantMirItems>
        let relevants = self.slicer.visit_path_tree(tree, target_block, checkpoint, property);

        relevants.iter().map(|items| {
            // 2. Inject caller contracts as path conditions
            // 3. Execute VM
            let mut vm_state = self.vm.execute(items)?;
            // 4. Apply caller contract facts as assertions
            for contract in caller_contracts {
                self.checker.assert_contract(&mut vm_state, contract);
            }
            // 5. Check property
            self.checker.check(&mut vm_state, checkpoint, property)
        }).collect()
    }
}
```

---

### 2.4 Refactored `call_summary/` — Call Summaries

The existing `CallEffect` enum stays but gets a companion method that knows how to
apply the effect to a VmState:

```rust
impl CallEffect {
    /// Apply this effect to the VM state.
    fn apply_to_vm_state(
        &self,
        state: &mut VmState,
        args: &[VmValue],
        dest: Local,
    );
}
```

Existing `fn_simulator.rs` entries gain a new field: `apply: fn(&mut VmState, &[VmValue], Local)`.
Initially this can be auto-derived from the existing `effects: Vec<CallEffect>`, then
gradually replaced with direct VM transforms for cases where the CallEffect abstraction
is insufficient.

---

## 3. Migration Strategy (5 Phases)

### Phase 1: Infrastructure (no behavior change)

- Create `src/verify/vm/` module skeleton
- Implement `VmState`, `VmValue`, `ValueInvariants` types
- Implement basic MIR executors: `Use`, `Ref`, `RawPtr`, `BinaryOp`, `UnaryOp`, `Cast`, `Goto`
- Create `PropertyChecker` skeleton with `check()` dispatch
- Add a `#[cfg(feature = "vm")]` feature flag gating the new code path

**Milestone:** New code compiles alongside old code, guarded by feature flag.

### Phase 2: Full MIR Coverage

- Implement remaining MIR executors: `Call`, `SwitchInt`, `Assert`, `StorageLive/Dead`,
  `Aggregate`, `Len`, `Discriminant`, `Drop`, `Repeat`, `NullaryOp`, `ShallowInitBox`,
  `CopyForDeref`, `ThreadLocalRef`
- Implement symbolic memory model: `allocate`, `address_of_place`
- Implement `CallEffect::apply_to_vm_state` for the current ~50 call summaries
- Add comprehensive unit tests for each executor (exec MIR snippet → verify VmState)

**Milestone:** VM can execute all retained MIR items for real-world examples.

### Phase 3: Property Checking

- Implement each `check_*` method in `PropertyChecker`
- For compound properties (`Deref`, `Ptr2Ref`, `ValidPtr`): implement decomposition
- Handle `for_each`, `or_alternatives`, contract `ContractExpr` lowering
- Run existing test suite under the feature flag, compare results with old pipeline
- Fix discrepancies

**Milestone:** All properties pass on existing test suite with comparable or better results.

### Phase 4: Parallel Run & Validation

- Add CLI flag `--verify-backend={legacy,vm}` with `legacy` as default
- Collect statistics: #proved, #failed, #unknown, runtime for both backends
- Run on the full benchmark suite (all functions with `#[rapx::verify]` annotations)
- Fix any regressions (proved by old, failed/unknown by new)

**Milestone:** VM backend matches or exceeds legacy backend on all metrics.

### Phase 5: Cleanup

- Remove old `ForwardVerifier` (`verifier.rs`, 2116 lines)
- Remove old `smt_check/` sub-modules (20 files, ~12000 lines total)
- Remove old `SmtModel` from `model.rs`
- Extract remaining shared utilities (const parsing, MIR helpers) into `helpers/`
- Remove feature flag, make VM the only backend
- Update documentation

**Milestone:** Codebase reduced by ~15000 lines, single unified verification path.

---

## 4. Design Decisions & Trade-offs

### 4.1 Memory model: Flat byte-level vs. typed object-level

**Decision:** Flat byte-level with provenance.

**Rationale:**
- Pointer arithmetic (`ptr.add(n)`) naturally maps to byte offsets
- Alignment checks work on byte addresses
- Bounds checks work on `[base, base + size)` intervals
- Z3 Array theory supports byte-level modeling efficiently
- Provenance (`AllocId`) prevents cross-allocation pointer confusion

**Trade-off:** Object-level reads (field access) require computing byte offsets from
type layout. This is explicit and correct but more verbose than a typed read.

### 4.2 Solver: Incremental vs. fresh per query

**Decision:** Incremental solver per VmState, with push/pop at checkpoints.

**Rationale:**
- The VM asserts facts (path conditions, known invariants) as it executes
- At each checkpoint, `solver.push()`, assert the negated property, `check()`, `solver.pop()`
- This avoids re-asserting all path facts for every property
- Z3 supports incremental solving efficiently

### 4.3 Loop handling: Bounded path enumeration (keep current approach)

**Decision:** Keep the current `PathEnumerator` + `allow_repeat` approach.

**Rationale:**
- The VM is a path executor, not a fixed-point abstract interpreter
- Loop invariants would be a separate feature (future work)
- Current bounded unrolling already works well for the targeted safety properties

### 4.4 Interprocedural: Summaries (keep current approach, refine)

**Decision:** Keep call summaries for external functions. For local callees,
add optional VM-based inlining with depth limit.

**Rationale:**
- External functions (std, alloc) have no MIR bodies — summaries are mandatory
- Local inlining is a natural extension of the VM: `exec_call` can optionally
  push a new frame and execute the callee body
- Depth limit (e.g., 1 level) prevents infinite recursion

### 4.5 Unsafe intrinsics and assembly

**Decision:** Conservative: if encountered, return `Unsupported` with diagnostic.

**Rationale:**
- `InlineAsm` has platform-specific semantics beyond what's needed for safety verification
- Intrinsics can be added as encountered, similar to current `fn_simulator` entries

---

## 5. File-level Summary

| File | Action | Lines (before → after) |
|---|---|---|
| `verifier.rs` | **Delete** | 2116 → 0 |
| `smt_check/common.rs` | **Rewrite** (just SmtChecker → PropertyChecker) | 4681 → ~300 |
| `smt_check/model.rs` | **Delete** (absorbed into `vm/state.rs`) | 4697 → 0 |
| `smt_check/align.rs` | **Delete** | ~120 → 0 |
| `smt_check/non_null.rs` | **Delete** | ~100 → 0 |
| `smt_check/allocated.rs` | **Delete** | ~200 → 0 |
| `smt_check/in_bound.rs` | **Delete** | ~400 → 0 |
| `smt_check/init.rs` | **Delete** | ~300 → 0 |
| `smt_check/valid_ptr.rs` | **Delete** | ~400 → 0 |
| `smt_check/alias.rs` | **Delete** | ~150 → 0 |
| `smt_check/alive.rs` | **Delete** | ~100 → 0 |
| `smt_check/typed.rs` | **Delete** | ~150 → 0 |
| `smt_check/owning.rs` | **Delete** | ~200 → 0 |
| `smt_check/non_overlap.rs` | **Delete** | ~200 → 0 |
| `smt_check/valid_num.rs` | **Delete** | ~100 → 0 |
| `smt_check/valid_cstr.rs` | **Delete** | ~300 → 0 |
| `smt_check/ptr2ref.rs` | **Delete** | ~200 → 0 |
| `smt_check/valid_transmute.rs` | **Delete** | ~300 → 0 |
| `smt_check/split_transmute.rs` | **Delete** | ~100 → 0 |
| `smt_check/field_invariant.rs` | **Delete** | ~200 → 0 |
| `smt_check/provenance.rs` | **Delete** | ~100 → 0 |
| `smt_check/init_range.rs` | **Delete** | ~100 → 0 |
| `verifier.rs` | **Delete** | 2116 → 0 |
| `slicer/` | **Keep** (minor adapt to new output interface) | ~800 → ~800 |
| `path_extractor.rs` | **Keep** | ~230 → ~230 |
| `contract/` | **Keep** | ~800 → ~800 |
| `call_summary/` | **Add** VmState transforms | ~800 → ~1000 |
| **NEW** `vm/mod.rs` | **Create** | 0 → ~150 |
| **NEW** `vm/state.rs` | **Create** | 0 → ~400 |
| **NEW** `vm/exec.rs` | **Create** | 0 → ~1200 |
| **NEW** `vm/memory.rs` | **Create** | 0 → ~300 |
| **NEW** `vm/call.rs` | **Create** | 0 → ~300 |
| **NEW** `vm/display.rs` | **Create** | 0 → ~100 |
| **NEW** `property_checker.rs` | **Create** | 0 → ~600 |
| `engine.rs` | **Simplify** | 140 → ~80 |
| `driver.rs` | **Minor adapt** | 1157 → ~1100 |
| **Net change** | | **~24000 → ~9000 lines** |

---

## 6. Risk Assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Z3 Array theory performance for memory model | Medium | Start with pointer-level only; add array reads/writes incrementally. Use Z3 `as-array` for constant folding. |
| Missing MIR construct causes VM fallback → Unknown | High (initially) | Phase 2 targets full MIR coverage. Any gaps return `Unsupported(reason)` with actionable diagnostic. |
| Call summary migration introduces bugs | Medium | Each summary gets both old `CallEffect` and new `apply_to_vm_state`; cross-check results in Phase 4. |
| Symbolic path explosion in VM | Low | Backward slicer already reduces items; path enumeration is bounded by `allow_repeat`. Same bounds apply. |
| Z3 version compatibility | Low | Same `z3` crate already in use. No API changes needed. |
