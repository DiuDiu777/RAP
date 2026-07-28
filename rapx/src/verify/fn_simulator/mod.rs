//! Function simulation: API behaviour modelling when MIR is unavailable.
//!
//! The [`registry`] module is the single source of truth — it maps API
//! name patterns to dependency/effect summaries (abstract interpretation)
//! and exposes name-based boolean helpers for classification queries.
//!
//! Consumers query through the public functions re-exported here, falling
//! back to MIR interprocedural analysis in [`super::call_summary`] when
//! the registry returns nothing.

pub mod registry;

pub use registry::{
    is_align_of, is_as_mut_ptr_range, is_as_ptr, is_as_ptr_range,
    is_byte_ptr_arith, is_element_ptr_arith, is_from_raw_parts, is_layout_constant,
    is_len, is_maybe_uninit_uninit, is_numeric_arith, is_option_unwrap,
    is_ownership_reconstruction, is_pointer_add, is_pointer_arithmetic, is_pointer_sub,
    is_ptr_cast, is_ptr_write, is_signed_ptr_arith, lookup_dependency, lookup_effect,
};
