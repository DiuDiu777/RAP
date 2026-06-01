# ordered_two_field_index

This crate is a two-step state-mutation test for contract-guided test generation.

The unsafe sink is:

```rust
unsafe { self.data.get_unchecked(self.idx) }
```

The hidden contract is `self.idx < self.data.len()`.  The invalid index is not
written directly into `idx`.  It must first be stored into `pending_idx`, then
committed into `idx`.

Triggering sequence:

```rust
let mut b = OrderedIndexBox::new(vec![1, 2, 3]);
b.set_pending_idx(usize::MAX);
b.commit_idx();
let _ = b.get();
```

Non-triggering variants:

```rust
// Missing the first mutation: idx remains 0.
b.commit_idx();
b.get();

// Missing the second mutation: idx remains 0.
b.set_pending_idx(usize::MAX);
b.get();

// Wrong order: commit copies the old pending_idx.
b.commit_idx();
b.set_pending_idx(usize::MAX);
b.get();
```

The intended CGAG path is:

```text
set_pending_idx --writes--> self.pending_idx
commit_idx      --uses----> self.pending_idx
commit_idx      --writes--> self.idx
self.idx        --InBound-> get
```
