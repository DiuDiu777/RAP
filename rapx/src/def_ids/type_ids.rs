//! Resolved `DefId`s of standard-library types used by verification.

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::sync::OnceLock;

static TYPES: OnceLock<Types> = OnceLock::new();

/// Standard-library ADT identities used by API classification, property
/// checks, and layout-sensitive analysis.
struct Types {
    box_types: Vec<DefId>,
    cstring_types: Vec<DefId>,
    string_types: Vec<DefId>,
    vec_types: Vec<DefId>,
    nonnull_types: Vec<DefId>,
    maybe_uninit_types: Vec<DefId>,
    ascii_char_types: Vec<DefId>,
    ordering_types: Vec<DefId>,
    iter_types: Vec<DefId>,
    rc_types: Vec<DefId>,
    sync_primitive_types: Vec<DefId>,
    index_range_types: Vec<DefId>,
    /// Negative auto-trait types (`Cell`/`UnsafeCell`/`RefCell`/`Ref`/`RefMut`/
    /// guards), keyed by short name — used by `ContainNoType` in Send/Sync obligations.
    negative_types: IndexMap<Box<str>, Vec<DefId>>,
}

pub fn init(tcx: TyCtxt) {
    TYPES.get_or_init(|| init_types(tcx));
}

fn init_types(tcx: TyCtxt) -> Types {
    let mut types = Types {
        box_types: Vec::new(),
        cstring_types: Vec::new(),
        string_types: Vec::new(),
        vec_types: Vec::new(),
        nonnull_types: Vec::new(),
        maybe_uninit_types: Vec::new(),
        ascii_char_types: Vec::new(),
        ordering_types: Vec::new(),
        iter_types: Vec::new(),
        rc_types: Vec::new(),
        sync_primitive_types: Vec::new(),
        index_range_types: Vec::new(),
        negative_types: IndexMap::new(),
    };

    // Real std types via diagnostic/lang items (`NonNull` only before rustc
    // 1.100, when it was still a diagnostic item).
    types.box_types.extend(tcx.lang_items().owned_box());
    types
        .cstring_types
        .extend(tcx.get_diagnostic_item(sym::cstring_type));
    types.vec_types.extend(tcx.get_diagnostic_item(sym::Vec));
    types.rc_types.extend(tcx.get_diagnostic_item(sym::Rc));
    // `core::cmp::Ordering` is `#[lang = "Ordering"]`.
    types
        .ordering_types
        .extend(tcx.lang_items().ordering_enum());
    // `core::mem::MaybeUninit` is `#[lang = "maybe_uninit"]`.
    types
        .maybe_uninit_types
        .extend(tcx.lang_items().maybe_uninit());
    // `core::cell::UnsafeCell` is `#[lang = "unsafe_cell"]`.
    if let Some(unsafe_cell) = tcx.lang_items().unsafe_cell_type() {
        types
            .negative_types
            .entry("UnsafeCell".into())
            .or_default()
            .push(unsafe_cell);
    }

    // Resolve standard-library ADTs by path, including `NonNull` and
    // `slice::Iter`/`IterMut`, which lack usable lang or diagnostic items.
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for adt in krate.adts() {
            let did = rustc_internal::internal(tcx, adt.def_id());
            let path = type_path(tcx, did, &krate.name, krate.is_local);
            collect_type_by_path(&mut types, &path, did);
        }
    }

    types
}

fn type_path(tcx: TyCtxt<'_>, did: DefId, crate_name: &str, is_local: bool) -> String {
    let path = tcx.def_path_str(did);
    if is_local && !path.starts_with(&format!("{crate_name}::")) {
        format!("{crate_name}::{path}")
    } else {
        path
    }
}

fn collect_type_by_path(types: &mut Types, name: &str, did: DefId) {
    let Some(group) = classify_type_path(name) else {
        return;
    };
    let ids = match group {
        TypeGroup::Vec => &mut types.vec_types,
        TypeGroup::String => &mut types.string_types,
        TypeGroup::Iter => &mut types.iter_types,
        TypeGroup::NonNull => &mut types.nonnull_types,
        TypeGroup::MaybeUninit => &mut types.maybe_uninit_types,
        TypeGroup::IndexRange => &mut types.index_range_types,
        TypeGroup::AsciiChar => &mut types.ascii_char_types,
        TypeGroup::Rc => &mut types.rc_types,
        TypeGroup::SyncPrimitive => &mut types.sync_primitive_types,
        TypeGroup::Negative(name) => types.negative_types.entry(name.into()).or_default(),
    };
    if !ids.contains(&did) {
        ids.push(did);
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TypeGroup {
    Vec,
    String,
    Iter,
    NonNull,
    MaybeUninit,
    IndexRange,
    AsciiChar,
    Rc,
    SyncPrimitive,
    Negative(&'static str),
}

fn classify_type_path(name: &str) -> Option<TypeGroup> {
    Some(match name {
        "alloc::vec::Vec" | "std::vec::Vec" => TypeGroup::Vec,
        "alloc::string::String" | "std::string::String" => TypeGroup::String,
        "core::slice::iter::Iter"
        | "core::slice::iter::IterMut"
        | "std::slice::Iter"
        | "std::slice::IterMut" => TypeGroup::Iter,
        "core::ptr::non_null::NonNull" | "std::ptr::NonNull" => TypeGroup::NonNull,
        "core::mem::maybe_uninit::MaybeUninit" | "std::mem::MaybeUninit" => TypeGroup::MaybeUninit,
        "core::ops::index_range::IndexRange"
        | "std::ops::index_range::IndexRange"
        | "std::ops::IndexRange" => TypeGroup::IndexRange,
        "core::ascii::ascii_char::AsciiChar" | "std::ascii::AsciiChar" => TypeGroup::AsciiChar,
        "alloc::rc::Rc" | "alloc::rcs::rc::Rc" | "std::rc::Rc" => TypeGroup::Rc,
        "core::cell::Cell" | "std::cell::Cell" => TypeGroup::Negative("Cell"),
        "core::cell::RefCell" | "std::cell::RefCell" => TypeGroup::Negative("RefCell"),
        "core::cell::Ref" | "std::cell::Ref" => TypeGroup::Negative("Ref"),
        "core::cell::RefMut" | "std::cell::RefMut" => TypeGroup::Negative("RefMut"),
        "std::sync::poison::mutex::Mutex"
        | "std::sync::nonpoison::mutex::Mutex"
        | "std::sync::poison::rwlock::RwLock"
        | "std::sync::nonpoison::rwlock::RwLock"
        | "std::sync::once_lock::OnceLock"
        | "std::sync::Mutex"
        | "std::sync::RwLock"
        | "std::sync::OnceLock" => TypeGroup::SyncPrimitive,
        "std::sync::poison::mutex::MutexGuard"
        | "std::sync::nonpoison::mutex::MutexGuard"
        | "std::sync::MutexGuard" => TypeGroup::Negative("MutexGuard"),
        "std::sync::poison::mutex::MappedMutexGuard"
        | "std::sync::nonpoison::mutex::MappedMutexGuard"
        | "std::sync::MappedMutexGuard" => TypeGroup::Negative("MappedMutexGuard"),
        "std::sync::poison::rwlock::RwLockWriteGuard"
        | "std::sync::nonpoison::rwlock::RwLockWriteGuard"
        | "std::sync::RwLockWriteGuard" => TypeGroup::Negative("RwLockWriteGuard"),
        _ if (name.starts_with("core::sync::atomic::")
            || name.starts_with("std::sync::atomic::"))
            && name.rsplit("::").next().is_some_and(|short| {
                matches!(
                    short,
                    "AtomicBool"
                        | "AtomicPtr"
                        | "AtomicI8"
                        | "AtomicI16"
                        | "AtomicI32"
                        | "AtomicI64"
                        | "AtomicI128"
                        | "AtomicIsize"
                        | "AtomicU8"
                        | "AtomicU16"
                        | "AtomicU32"
                        | "AtomicU64"
                        | "AtomicU128"
                        | "AtomicUsize"
                )
            }) =>
        {
            TypeGroup::SyncPrimitive
        }
        _ => return None,
    })
}

fn types() -> &'static Types {
    TYPES.get().expect("Type DefIds haven't been initialized.")
}

macro_rules! type_predicates {
    ($( $(#[$attr:meta])* $name:ident => $field:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name(did: DefId) -> bool {
                types().$field.contains(&did)
            }
        )+
    };
}

type_predicates! {
    /// Whether this is `alloc::boxed::Box`.
    is_std_box => box_types,
    /// Whether this is `alloc::ffi::CString`.
    is_std_cstring => cstring_types,
    /// Whether this is `alloc::vec::Vec`.
    is_std_vec => vec_types,
    /// Whether this is `alloc::string::String`.
    is_std_string => string_types,
    /// Whether this is `core::ptr::NonNull`.
    is_std_nonnull => nonnull_types,
    /// Whether this is `core::mem::MaybeUninit`.
    is_maybe_uninit_type => maybe_uninit_types,
    /// Whether this is `core::cmp::Ordering`.
    is_std_ordering => ordering_types,
    /// Whether this is `core::slice::Iter` or `IterMut`.
    is_std_iter_or_itermut => iter_types,
    /// Whether this is `alloc::rc::Rc`.
    is_std_rc => rc_types,
    /// Whether this is a standard `Mutex`, `RwLock`, `OnceLock`, or atomic type.
    is_std_sync_primitive => sync_primitive_types,
    /// Whether this is the standard `IndexRange` type.
    is_index_range => index_range_types,
}

/// The `AsciiChar` definition used to resolve its short name in contracts.
pub fn ascii_char_type() -> Option<DefId> {
    types().ascii_char_types.first().copied()
}

/// Resolve a negative-type name (as written in `std-trait.json`) to its
/// resolved `DefId` set. Unknown or unresolved names return `None`.
pub fn negative_type_defs(name: &str) -> Option<&'static [DefId]> {
    let ids = match name {
        "Rc" => types().rc_types.as_slice(),
        "NonNull" => types().nonnull_types.as_slice(),
        _ => types().negative_types.get(name)?.as_slice(),
    };
    (!ids.is_empty()).then_some(ids)
}
