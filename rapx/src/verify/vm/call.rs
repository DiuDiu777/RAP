//! Call handling for the symbolic VM.
//!
//! Bridges the existing call summary infrastructure (`call_summary`)
//! with the new symbolic VM state. The `exec_call` method is called
//! from `exec.rs` when a `Call` terminator is encountered.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand};
use z3::ast::{Ast, Int};

use crate::compat::Spanned;
use crate::verify::call_summary::{self, CallEffect};

use super::state::{AllocId, Provenance, VmState, VmValue, ValueInvariants};

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Execute a call terminator using call summaries.
    pub fn exec_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
        _target: Option<BasicBlock>,
        _cleanup: Option<BasicBlock>,
        caller_def_id: DefId,
    ) {
        let arg_values: Vec<VmValue<'ctx, 'tcx>> = args
            .iter()
            .map(|arg| self.value_of_operand(&arg.node))
            .collect();

        let summary = call_summary::effect_summary(
            self.tcx,
            caller_def_id,
            func,
            destination,
        );

        self.last_call_name = summary.name.clone();

        if summary.unsupported {
            self.notes.push(format!("unsupported call: {}", summary.name));
            let dest_ty = self.body.local_decls[destination].ty;
            self.set_local(
                destination,
                VmValue {
                    term: self.fresh_int(&format!("callret_{}", destination.as_usize())),
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                },
            );
            return;
        }

        for effect in &summary.effects {
            self.apply_call_effect(effect, &arg_values, destination);
        }

        // After applying call effects, try to materialize constant bytes
        // from the source operands (e.g. as_ptr() on a constant byte array).
        // This enables byte-level ValidCStr checks for static byte strings.
        if let Some(mut dv) = self.locals.get(&destination).cloned() {
            let dest_ty = dv.ty;
            let pointee_is_byte_like = match dest_ty.kind() {
                rustc_middle::ty::TyKind::RawPtr(inner, _)
                | rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                    match inner.kind() {
                        rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                        | rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8) => true,
                        rustc_middle::ty::TyKind::Array(elem_ty, _)
                        | rustc_middle::ty::TyKind::Slice(elem_ty) => {
                            matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8))
                        }
                        _ => false,
                    }
                }
                _ => false,
            };
            if pointee_is_byte_like {
                for arg in args {
                    self.try_materialize_const_bytes(&mut dv, &arg.node);
                    if dv.provenance.is_some() {
                        self.set_local(destination, dv);
                        break;
                    }
                }
            }
        }
    }

    /// Apply a single call effect to the VM state.
    fn apply_call_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'ctx, 'tcx>],
        dest: Local,
    ) {
        match effect {
            CallEffect::ReturnAliasArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.non_null = true;
                    val.invariants.aligned = true;
                    val.invariants.init = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerFromArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    let dest_ty = self.body.local_decls[dest].ty;
                    val.ty = dest_ty;
                    val.invariants.non_null = true;
                    val.invariants.aligned = true;
                    // Pointer-returning APIs expose the backing allocation;
                    // mark it init-accessible for raw pointer types.
                    if matches!(dest_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
                        val.invariants.init = true;
                    }
                    // For locally-created Vec: redirect as_ptr() from the
                    // struct allocation to the heap data allocation.
                    let is_vec = self.last_call_name.contains("::Vec")
                        || self.last_call_name.contains("::CString");
                    if is_vec {
                        if let Some(ref prov) = val.provenance {
                            if let Some(data_alloc) = self.slice_data_allocations.get(&prov.alloc_id).copied() {
                                if let Some(data_base) = self.allocation_base(data_alloc).cloned() {
                                    val.term = data_base;
                                    val.provenance = Some(Provenance {
                                        alloc_id: data_alloc,
                                        offset: Int::from_u64(self.ctx, 0),
                                    });
                                }
                            }
                        }
                    }
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerAdd { base_arg, offset_arg, stride } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let adjusted_offset = if stride_bytes == 1 {
                        Int::add(self.ctx, &[&offset.term])
                    } else {
                        let stride_term = Int::from_u64(self.ctx, stride_bytes);
                        Int::mul(self.ctx, &[&offset.term, &stride_term])
                    };
                    let new_term = Int::add(self.ctx, &[&base.term, &adjusted_offset]);
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| {
                        Provenance {
                            alloc_id: prov.alloc_id,
                            offset: Int::add(self.ctx, &[&prov.offset, &adjusted_offset]),
                        }
                    });
                    // Preserve alignment if the added offset is compatible
                    let align_n = self.compute_pointer_add_align(base, offset, stride_bytes);
                    let val = VmValue {
                        term: new_term,
                        ty: self.body.local_decls[dest].ty,
                        provenance: adjusted_provenance,
                        invariants: ValueInvariants {
                            aligned: align_n.is_some() && base.invariants.aligned,
                            in_bounds: base.invariants.in_bounds,
                            align_n,
                            ..base.invariants
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerSub { base_arg, offset_arg, stride } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let stride_term = Int::from_u64(self.ctx, stride_bytes);
                    let scaled = Int::mul(self.ctx, &[&offset.term, &stride_term]);
                    let new_term = Int::sub(self.ctx, &[&base.term, &scaled]);
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| {
                        Provenance {
                            alloc_id: prov.alloc_id,
                            offset: Int::sub(self.ctx, &[&prov.offset, &scaled]),
                        }
                    });
                    let align_n = self.compute_pointer_add_align(base, offset, stride_bytes);
                    let val = VmValue {
                        term: new_term,
                        ty: self.body.local_decls[dest].ty,
                        provenance: adjusted_provenance,
                        invariants: ValueInvariants {
                            aligned: align_n.is_some() && base.invariants.aligned,
                            in_bounds: base.invariants.in_bounds,
                            align_n,
                            ..base.invariants
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnNonZero => {
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.non_null = true;
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_nz_{}", dest.as_usize()));
                    self.set_local(dest, VmValue {
                        term, ty: dest_ty, provenance: None,
                        invariants: ValueInvariants { non_null: true, ..Default::default() },
                    });
                }
            }
            CallEffect::ReturnAligned { align: _, ty_name: _ } => {
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.aligned = true;
                    existing.invariants.non_null = true;
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_align_{}", dest.as_usize()));
                    self.set_local(dest, VmValue {
                        term, ty: dest_ty, provenance: None,
                        invariants: ValueInvariants { aligned: true, non_null: true, ..Default::default() },
                    });
                }
            }
            CallEffect::ReturnLengthOfArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let effective_alloc_id = arg_val.provenance_alloc_id()
                        .and_then(|pid| self.slice_data_allocations.get(&pid).copied())
                        .or_else(|| arg_val.provenance_alloc_id());

                    if let Some(alloc_id) = effective_alloc_id {
                        let dest_ty = self.body.local_decls[dest].ty;
                        // If the allocation has an element type, divide the
                        // byte-aligned size by the element size to return the
                        // number of elements (e.g. slice length).
                        if let Some(elem_ty) = self.allocations.iter().find(|a| a.id == alloc_id).and_then(|a| a.element_ty) {
                            let elem_size = self.size_of_ty(elem_ty) as u64;
                            if elem_size > 1 {
                                if let Some(size) = self.allocation_size(alloc_id) {
                                    let div = Int::from_u64(self.ctx, elem_size);
                                    let val = VmValue {
                                        term: size.div(&div),
                                        ty: dest_ty,
                                        provenance: None,
                                        invariants: ValueInvariants::default(),
                                    };
                                    self.set_local(dest, val);
                                    return;
                                }
                            } else if let Some(size) = self.allocation_size(alloc_id) {
                                let val = VmValue {
                                    term: size.clone(),
                                    ty: dest_ty,
                                    provenance: None,
                                    invariants: ValueInvariants::default(),
                                };
                                self.set_local(dest, val);
                                return;
                            }
                        } else if let Some(size) = self.allocation_size(alloc_id) {
                            let val = VmValue {
                                term: size.clone(),
                                ty: dest_ty,
                                provenance: None,
                                invariants: ValueInvariants::default(),
                            };
                            self.set_local(dest, val);
                            return;
                        }
                    }
                }
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("len_{}", dest.as_usize()));
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnConst { value, label: _ } => {
                let dest_ty = self.body.local_decls[dest].ty;
                let term = Int::from_u64(self.ctx, *value);
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("min_{}", dest.as_usize()));
                    self.path_conditions.push(term.le(&lhs.term));
                    self.path_conditions.push(term.le(&rhs.term));
                    let eq_lhs = term._eq(&lhs.term);
                    let eq_rhs = term._eq(&rhs.term);
                    self.path_conditions
                        .push(z3::ast::Bool::or(self.ctx, &[&eq_lhs, &eq_rhs]));
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg) {
                    if let Some(prov) = &arg_val.provenance {
                        // For locally-created Vec-like types: create a heap data
                        // allocation on first mutation. (Param Vecs already have
                        // an external allocation set by init_parameters.)
                        let is_vec = crate::verify::call_summary::fn_simulator::is_vec_push(&self.last_call_name);
                        let is_external = self.allocations.iter()
                            .any(|a| a.id == prov.alloc_id && a.is_external);
                        if is_vec && !is_external {
                            if let Some(old_data) = self.slice_data_allocations.get(&prov.alloc_id).copied() {
                                // Subsequent mutation: invalidate old heap data.
                                self.dead_allocations.insert(old_data);
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) = self.allocate_external(max_size, 1, None);
                                self.slice_data_allocations.insert(prov.alloc_id, data_alloc);
                            } else {
                                // First mutation: create heap data allocation.
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) = self.allocate_external(max_size, 1, None);
                                self.slice_data_allocations.insert(prov.alloc_id, data_alloc);
                            }
                        }
                        // When offset is concrete, only mark the bytes actually
                        // written. For symbolic offsets, mark entire allocation.
                        let off_u64 = prov.offset.as_u64()
                            .or_else(|| prov.offset.simplify().as_u64());
                        if let Some(off) = off_u64 {
                            if off == 0 {
                                self.init_allocations.insert(prov.alloc_id);
                            }
                            let elem_size = match arg_val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => self.size_of_ty(*inner) as usize,
                                _ => 0,
                            };
                            let write_size = if elem_size > 0 { elem_size } else {
                                self.allocation_size(prov.alloc_id).and_then(|s| s.as_u64()).unwrap_or(0) as usize
                            };
                            let end = (off as usize + write_size).min(4096);
                            for byte_off in (off as usize)..end {
                                self.byte_init.insert((prov.alloc_id, byte_off));
                            }
                        } else {
                            if prov.offset.as_u64() == Some(0) {
                                self.init_allocations.insert(prov.alloc_id);
                            }
                            if let Some(size) = self.allocation_size(prov.alloc_id).cloned() {
                                if let Some(size_val) = size.as_u64() {
                                    for off in 0..(size_val as usize).min(1024) {
                                        self.byte_init.insert((prov.alloc_id, off));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            CallEffect::ReadMemory { arg: _ } => {
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("read_{}", dest.as_usize()));
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnFreshAllocation { pointer_arg, size_arg, elem_size } => {
                if let (Some(ptr_val), Some(size_val)) = (args.get(*pointer_arg), args.get(*size_arg)) {
                    let elem_sz = Int::from_u64(self.ctx, *elem_size);
                    let total = Int::mul(self.ctx, &[&size_val.term, &elem_sz]);
                    let total_u64 = total.as_u64();
                    let (alloc_id, _base) = self.allocate(total, *elem_size, None);
                    let dest_ty = self.body.local_decls[dest].ty;
                    let prov = Provenance {
                        alloc_id,
                        offset: ptr_val.provenance.as_ref()
                            .map(|p| p.offset.clone())
                            .unwrap_or_else(|| Int::from_u64(self.ctx, 0)),
                    };
                    // If return is a reference, register slice/pointee data
                    if let Some(ref dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                        self.slice_data_allocations.insert(dest_alloc_id.clone(), alloc_id);
                    }
                    // Propagate init status and byte-level tracking from the source pointer
                    let mut is_init = false;
                    if let Some(ref source_prov) = ptr_val.provenance {
                        // Only propagate init_allocations if the source allocation
                        // covers the required byte range
                        if self.init_allocations.contains(&source_prov.alloc_id) {
                            let source_size = self.allocation_size(source_prov.alloc_id).cloned();
                            let source_u64 = source_size.as_ref().and_then(|s| s.as_u64());
                            if let Ok(mut f) = std::fs::OpenOptions::new().append(true).create(true).open("/tmp/vm_debug.log") {
                                use std::io::Write;
                                let _ = writeln!(f, "ReturnFreshAlloc: total={:?} source_size={:?} match={}",
                                    total_u64, source_u64, total_u64.map_or(false, |t| source_u64.map_or(false, |s| t <= s)));
                            }
                            if let (Some(total_bytes), Some(source_bytes)) = (total_u64, source_u64) {
                                if total_bytes <= source_bytes {
                                    self.init_allocations.insert(alloc_id);
                                    is_init = true;
                                }
                            }
                        }
                        // Copy byte-level tracking
                        let byte_pairs: Vec<_> = self.byte_values.iter()
                            .filter(|((aid, _), _)| *aid == source_prov.alloc_id)
                            .map(|((_, off), term)| (*off, term.clone()))
                            .collect();
                        for (off, term) in byte_pairs {
                            self.record_byte_value(alloc_id, off, term);
                        }
                        let init_bytes: Vec<_> = self.byte_init.iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in init_bytes {
                            self.byte_init.insert((alloc_id, off));
                        }
                        let nul_offs: Vec<_> = self.known_nul_offsets.iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in nul_offs {
                            self.known_nul_offsets.insert((alloc_id, off));
                        }
                        let non_nul_offs: Vec<_> = self.known_non_nul_offsets.iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in non_nul_offs {
                            self.known_non_nul_offsets.insert((alloc_id, off));
                        }
                    }
                    self.set_local(dest, VmValue {
                        term: ptr_val.term.clone(),
                        ty: dest_ty,
                        provenance: Some(prov),
                        invariants: ValueInvariants {
                            non_null: true, init: is_init, in_bounds: true, aligned: true,
                            ..ValueInvariants::default()
                        },
                    });
                }
            }
            CallEffect::OwnsInitMemory { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(prov) = &arg_val.provenance {
                        self.init_allocations.insert(prov.alloc_id);
                    }
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.init = true;
                    val.invariants.non_null = true;
                    self.set_local(dest, val);
                }
            }
            _ => {
                self.notes.push(format!("unhandled call effect: {:?}", effect));
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("unk_{}", dest.as_usize()));
                self.set_local(
                    dest,
                    VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    },
                );
            }
        }
    }

    /// Compute the preserved alignment when doing `base + offset * stride`.
    /// If stride is a multiple of known alignment, the result has that alignment.
    fn compute_pointer_add_align(
        &self,
        base: &VmValue<'ctx, 'tcx>,
        _offset: &VmValue<'ctx, 'tcx>,
        stride_bytes: u64,
    ) -> Option<u64> {
        let base_align = base.invariants.align_n;
        if let Some(n) = base_align {
            if stride_bytes > 0 && stride_bytes % n == 0 {
                return Some(n);
            }
        }
        // If stride itself is a power of two, the step preserves that alignment
        if stride_bytes > 1 && stride_bytes.is_power_of_two() {
            if base_align.map_or(true, |a| stride_bytes >= a && stride_bytes % a == 0) {
                return Some(stride_bytes.min(base_align.unwrap_or(stride_bytes)));
            }
        }
        None
    }

    pub(crate) fn propagate_const_bytes_to_tracked(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
    ) {
        let mut const_bytes: Option<(Vec<u8>, usize)> = None;
        let mut tracked_alloc: Option<AllocId> = None;
        let mut tracked_offset: usize = 0;

        for (i, arg) in args.iter().enumerate() {
            let arg_val = self.value_of_operand(&arg.node);
            if const_bytes.is_none() {
                let bytes_opt = super::state::extract_const_bytes_from_operand(
                    self.tcx,
                    &arg.node,
                ).or_else(|| self.trace_to_const_bytes(&arg.node));
                if let Some(bytes) = bytes_opt {
                    const_bytes = Some((bytes, i));
                }
            }
            if tracked_alloc.is_none() {
                if let Some(alloc_id) = arg_val.provenance_alloc_id() {
                    tracked_alloc = Some(alloc_id);
                    if let Some(ref prov) = arg_val.provenance {
                        tracked_offset = prov.offset.as_u64().map(|v| v as usize).unwrap_or(0);
                    }
                }
            }
        }

        if let (Some((bytes, _)), Some(alloc_id)) = (const_bytes, tracked_alloc) {
            for (j, &b) in bytes.iter().enumerate() {
                let off = tracked_offset + j;
                self.record_byte_value(
                    alloc_id,
                    off,
                    Int::from_u64(self.ctx, b as u64),
                );
                if b == 0 {
                    self.known_nul_offsets.insert((alloc_id, off));
                } else {
                    self.known_non_nul_offsets.insert((alloc_id, off));
                }
            }
            self.init_allocations.insert(alloc_id);
        }
    }
}
