//! Decomposition rules for compound safety properties.
//!
//! This module centralises the relationship between compound safety properties
//! (ValidPtr, Deref, Ptr2Ref, Layout) and their primitive constituents, as
//! defined in `safety-tags/primitive-sp.md` §2.2.
//!
//! Every SMT checker that processes a compound SP should obtain the primitive
//! list from this module rather than hard-coding the decomposition.

use super::types::PropertyKind;
use super::types::Property;

/// Reuse the argument structure of an original property while replacing its
/// kind for primitive-component checking.  `null_guard` and `or_alternatives`
/// are cleared because primitives are always plain properties.
pub fn with_kind<'tcx>(property: &Property<'tcx>, kind: PropertyKind) -> Property<'tcx> {
    Property {
        kind,
        args: property.args.clone(),
        contract_kind: property.contract_kind,
        null_guard: None,
        or_alternatives: Vec::new(),
    }
}

/// Return the primitive SPs that a compound SP is composed of.
///
/// Returns `None` for primitive SPs that are not defined as compounds.
/// The order of the returned slice is the canonical decomposition order.
pub fn primitive_components(kind: &PropertyKind) -> Option<&'static [PropertyKind]> {
    Some(match kind {
        // §2.2: Deref(p, T, n) = Allocated(p, T, n, *) && InBound(p, T, n)
        PropertyKind::Deref => &[PropertyKind::Allocated, PropertyKind::InBound],

        // §2.2: Ptr2Ref(p, T) = Init(p, T, 1) && Align(p, T) && Alias(p, ret)
        PropertyKind::Ptr2Ref => &[PropertyKind::Init, PropertyKind::Align, PropertyKind::Alias],

        // §2.2: Layout(p, layout) = ValidNum(...) && Allocated(p, u8, layout.size, heap)
        PropertyKind::Layout => &[PropertyKind::Allocated],

        // ValidPtr is conditional on type size and thus handled
        // separately by the ValidPtr checker; its non-ZST arm
        // delegates to Deref which is fully covered above.
        _ => return None,
    })
}

/// Check whether `declared` implies `required` — used in struct-invariant
/// resolution to avoid re-checking a property that is already guaranteed by
/// a stronger declared invariant.
///
/// Current implications:
/// - `Init ⇒ Typed` (§3.3.3: Init implies the type invariant)
/// - `InBound ⇒ Allocated` (§3.2.1: a range inside an allocated object is
///   necessarily allocated by that object's allocator)
/// - `ValidPtr ⇒ Allocated` and `ValidPtr ⇒ InBound` (for non‑ZST,
///   `ValidPtr = Deref = Allocated && InBound`)
pub fn kind_implies(declared: &PropertyKind, required: &PropertyKind) -> bool {
    // Identity
    if declared == required {
        return true;
    }
    // Init ⇒ Typed
    if matches!(declared, PropertyKind::Init) && matches!(required, PropertyKind::Typed) {
        return true;
    }
    // InBound ⇒ Allocated
    if matches!(declared, PropertyKind::InBound)
        && matches!(required, PropertyKind::Allocated)
    {
        return true;
    }
    // ValidPtr ⇒ Allocated | InBound  (non-ZST; caller guards the ZST case)
    if matches!(declared, PropertyKind::ValidPtr)
        && matches!(required, PropertyKind::Allocated | PropertyKind::InBound)
    {
        return true;
    }
    // Compound SPs ⇒ each of their primitive components
    // (§2.2: Deref ⇒ Allocated && InBound, Ptr2Ref ⇒ Init && Align && Alias, etc.)
    if let Some(primitives) = primitive_components(declared) {
        if primitives.contains(required) {
            return true;
        }
    }
    false
}
