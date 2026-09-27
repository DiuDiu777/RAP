//! Region (lifetime) helpers shared by the VM and the property checker.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyParamRegion, GenericParamDefKind, Region, RegionKind, Ty, TyCtxt};

/// Resolve a lifetime name from a contract (e.g. `"a"`, `"static"`) to a
/// concrete `Region`. `name` is the raw ident, without the leading `'`.
pub(crate) fn resolve_region_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
) -> Option<Region<'tcx>> {
    if name == "static" || name == "static_lifetime" {
        return Some(tcx.lifetimes.re_static);
    }
    let ticked = format!("'{name}");
    let generics = tcx.generics_of(def_id);
    for param in &generics.own_params {
        if matches!(param.kind, GenericParamDefKind::Lifetime)
            && (param.name.as_str() == name || param.name.as_str() == ticked.as_str())
        {
            return Some(Region::new_early_param(
                tcx,
                EarlyParamRegion {
                    index: param.index,
                    name: param.name,
                },
            ));
        }
    }
    None
}

/// Whether `src` outlives `ret` (`src: ret`).
///
/// `'static` and reflexivity are handled structurally; declared where-clauses
/// (`'a: 'b`) are resolved via rustc's `FreeRegionMap` (which also computes the
/// transitive closure). Anything else is treated as *not* outlives.
pub(crate) fn region_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    src: Region<'tcx>,
    ret: Region<'tcx>,
) -> bool {
    match (src.kind(), ret.kind()) {
        (RegionKind::ReStatic, _) => true,
        (_, RegionKind::ReStatic) => false,
        _ => {
            if src == ret {
                return true;
            }
            if !src.is_free() || !ret.is_free() {
                return false;
            }
            free_region_outlives(tcx, def_id, src, ret)
        }
    }
}

/// Consult the function's declared outlives constraints (where-clauses) via
/// rustc's `FreeRegionMap`, which records `'a: 'b` bounds and their transitive
/// closure. `sub_free_regions(r_a, r_b)` tests `r_a <= r_b` (i.e. `r_b: r_a`),
/// so `src: ret` is `sub_free_regions(ret, src)`.
fn free_region_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    src: Region<'tcx>,
    ret: Region<'tcx>,
) -> bool {
    use rustc_data_structures::fx::FxHashSet;
    use rustc_infer::infer::outlives::env::OutlivesEnvironment;

    let param_env = tcx.param_env(def_id);
    let env = OutlivesEnvironment::from_normalized_bounds(
        param_env,
        Vec::new(),
        std::iter::empty(),
        FxHashSet::default(),
    );
    env.free_region_map().sub_free_regions(tcx, ret, src)
}

/// Whether `src_region` provably outlives the reference region of `self_ty`
/// via the type's own well-formedness.  A reference parameter `&'r SliceHost<'s>`
/// requires its pointee's regions to outlive `'r` (`'s: 'r`), which the
/// where-clause-only [`region_outlives`] cannot see.  Complements it with the
/// implied outlives components of `self_ty`.
pub(crate) fn region_outlives_implied<'tcx>(
    tcx: TyCtxt<'tcx>,
    src_region: Region<'tcx>,
    self_ty: Ty<'tcx>,
) -> bool {
    use rustc_data_structures::smallvec::SmallVec;
    use rustc_middle::ty::outlives::{Component, push_outlives_components};

    let mut out: SmallVec<[Component<TyCtxt<'tcx>>; 4]> = SmallVec::new();
    push_outlives_components(tcx, self_ty, &mut out);
    out.iter()
        .any(|c| matches!(c, Component::Region(r) if *r == src_region))
}

/// The function's signature with late-bound regions liberated to free
/// `ReLateParam`s, so reference regions are comparable (MIR erases them to
/// `ReErased`).
fn liberate_fn_sig<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> rustc_middle::ty::FnSig<'tcx> {
    let fn_sig = tcx.fn_sig(def_id).instantiate_identity();
    #[cfg(rapx_ge_99)]
    let fn_sig = fn_sig.skip_norm_wip();
    tcx.liberate_late_bound_regions(def_id, fn_sig)
}

/// The reference region of `def_id`'s return type (`&'r T` → `Some('r)`).
pub(crate) fn fn_return_region<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Region<'tcx>> {
    use rustc_middle::ty::TyKind;
    match liberate_fn_sig(tcx, def_id).output().kind() {
        TyKind::Ref(region, _, _) => Some(*region),
        _ => None,
    }
}

/// The type of `def_id`'s argument at `index`.
pub(crate) fn fn_arg_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, index: usize) -> Option<Ty<'tcx>> {
    liberate_fn_sig(tcx, def_id).inputs().get(index).copied()
}
