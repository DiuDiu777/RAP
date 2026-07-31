
#[test]
fn linked_list_nonnull() {
    let output = run_with_args("verify_cases/linked_list_nonnull", CMD_VERIFY);

    assert_function_result(&output, "LinkedList::<T>::new", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::len", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::is_empty", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::push_back", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::push_front", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::pop_front", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::pop_back", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::clear", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::from_vec", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::front", "UNSOUND");
    assert_function_result(&output, "LinkedList::<T>::back", "UNSOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::front_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::back_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::front_mut_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::back_mut_copy", "SOUND");
    assert_function_result(
        &output,
        "<LinkedList<T> as std::ops::Drop>::drop",
        "SOUND",
    );

    assert_function_result(&output, "LinkedList::<T>::front_mut", "UNSOUND");
    assert_function_result(&output, "LinkedList::<T>::back_mut", "UNSOUND");
}

#[test]
fn linked_list_nonnull_skip_invariant() {
    let output = run_with_args(
        "verify_cases/linked_list_nonnull",
        CMD_VERIFY_SKIP_INVARIANT,
    );

    let unsound_fns = ["front", "back", "front_mut", "back_mut"];
    let mut result_by_fn: std::collections::BTreeMap<&str, Vec<(&str, bool)>> =
        std::collections::BTreeMap::new();

    let mut current_seq: Option<&str> = None;
    let mut current_result: Option<&str> = None;
    for line in output.lines() {
        if let Some(pos) = line.find("[rapx::verify] sequence:") {
            if let Some(seq) = current_seq.take() {
                let r = current_result.take().unwrap_or("");
                let fn_name = seq.rsplit(" -> ").next().unwrap_or(seq);
                let is_unsound = unsound_fns.contains(&fn_name);
                result_by_fn.entry(fn_name).or_default().push((r, is_unsound));
            }
            current_seq = Some(line[pos + "[rapx::verify] sequence:".len()..].trim());
        }
        if let Some(res_pos) = line.find("result:") {
            current_result = Some(line[res_pos..].trim());
        }
    }
    if let Some(seq) = current_seq {
        let r = current_result.unwrap_or("");
        let fn_name = seq.rsplit(" -> ").next().unwrap_or(seq);
        let is_unsound = unsound_fns.contains(&fn_name);
        result_by_fn.entry(fn_name).or_default().push((r, is_unsound));
    }

    for (fn_name, results) in &result_by_fn {
        let is_unsound_fn = unsound_fns.contains(fn_name);
        let total = results.len();
        let unsound_count = results.iter().filter(|(r, _)| r.contains("UNSOUND")).count();
        let sound_count = results.iter().filter(|(r, _)| r.contains("SOUND")).count();

        assert!(total > 0, "no sequences found for reading function: {fn_name}");

        if is_unsound_fn {
            assert_eq!(
                unsound_count, total,
                "expected all {total} sequences for {fn_name} to be UNSOUND, got {unsound_count} UNSOUND / {sound_count} SOUND"
            );
        } else {
            assert_eq!(
                sound_count, total,
                "expected all {total} sequences for {fn_name} to be SOUND, got {sound_count} SOUND / {unsound_count} UNSOUND"
            );
        }
    }
}

#[test]
fn linked_list_rawptr_skip_invariant() {
    let output = run_with_args(
        "verify_cases/linked_list_rawptr",
        CMD_VERIFY_SKIP_INVARIANT,
    );

    let unsound_fns = ["front", "back", "front_mut", "back_mut"];
    let mut result_by_fn: std::collections::BTreeMap<&str, Vec<(&str, bool)>> =
        std::collections::BTreeMap::new();

    let mut current_seq: Option<&str> = None;
    let mut current_result: Option<&str> = None;
    for line in output.lines() {
        if let Some(pos) = line.find("[rapx::verify] sequence:") {
            if let Some(seq) = current_seq.take() {
                let r = current_result.take().unwrap_or("");
                let fn_name = seq.rsplit(" -> ").next().unwrap_or(seq);
                let is_unsound = unsound_fns.contains(&fn_name);
                result_by_fn.entry(fn_name).or_default().push((r, is_unsound));
            }
            current_seq = Some(line[pos + "[rapx::verify] sequence:".len()..].trim());
        }
        if let Some(res_pos) = line.find("result:") {
            current_result = Some(line[res_pos..].trim());
        }
    }
    if let Some(seq) = current_seq {
        let r = current_result.unwrap_or("");
        let fn_name = seq.rsplit(" -> ").next().unwrap_or(seq);
        let is_unsound = unsound_fns.contains(&fn_name);
        result_by_fn.entry(fn_name).or_default().push((r, is_unsound));
    }

    for (fn_name, results) in &result_by_fn {
        let is_unsound_fn = unsound_fns.contains(fn_name);
        let total = results.len();
        let unsound_count = results.iter().filter(|(r, _)| r.contains("UNSOUND")).count();
        let sound_count = results.iter().filter(|(r, _)| r.contains("SOUND")).count();

        assert!(total > 0, "no sequences found for reading function: {fn_name}");

        if is_unsound_fn {
            assert_eq!(
                unsound_count, total,
                "expected all {total} sequences for {fn_name} to be UNSOUND, got {unsound_count} UNSOUND / {sound_count} SOUND"
            );
        } else {
            assert_eq!(
                sound_count, total,
                "expected all {total} sequences for {fn_name} to be SOUND, got {sound_count} SOUND / {unsound_count} UNSOUND"
            );
        }
    }
}

#[test]
fn linked_list_rawptr() {
    let output = run_with_args("verify_cases/linked_list_rawptr", CMD_VERIFY);

    assert_function_result(&output, "LinkedList::<T>::new", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::len", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::is_empty", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::push_back", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::push_front", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::pop_front", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::pop_back", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::clear", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::from_vec", "SOUND");
    assert_function_result(&output, "LinkedList::<T>::front", "UNSOUND");
    assert_function_result(&output, "LinkedList::<T>::back", "UNSOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::front_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::back_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::front_mut_copy", "SOUND");
    assert_function_result(&output, "LinkedList::<T: Copy>::back_mut_copy", "SOUND");
    assert_function_result(
        &output,
        "<LinkedList<T> as std::ops::Drop>::drop",
        "SOUND",
    );

    assert_unproved_exclusive_with_result(
        &output,
        "LinkedList::<T>::front_mut",
        &["Alias"],
        "HAZARD",
    );
    assert_unproved_exclusive_with_result(
        &output,
        "LinkedList::<T>::back_mut",
        &["Alias"],
        "HAZARD",
    );
}

#[test]
fn linked_list_rawptr_no_phantomdata() {
    let output = run_with_args("verify_cases/linked_list_rawptr_no_phantomdata", CMD_VERIFY);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn linked_list_nonnull_no_phantomdata() {
    let output = run_with_args("verify_cases/linked_list_nonnull_no_phantomdata", CMD_VERIFY);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn std_challenge_17() {
    let output = run_with_args("verify_cases/std-challenge-17", CMD_VERIFY_TARGETED);

    let functions = [
        "<[T] as SliceExt<T>>::get_unchecked_ext",
        "<[T] as SliceExt<T>>::get_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::split_at_unchecked_ext",
        "<[T] as SliceExt<T>>::split_at_mut_unchecked_ext",
        "<[T] as SliceExt<T>>::swap_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::align_to_ext",
        "<[T] as SliceExt<T>>::align_to_mut_ext",
        "<[T] as SliceExt<T>>::get_disjoint_unchecked_mut_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_rchunks_ext",
        "<[T] as SliceSafeExt<T>>::split_at_checked_ext",
        "<[T] as SliceSafeExt<T>>::split_at_mut_checked_ext",
        "<[T] as SliceSafeExt<T>>::reverse_ext",
        "<[T] as SliceSafeExt<T>>::rotate_left_ext",
        "<[T] as SliceSafeExt<T>>::rotate_right_ext",
        "<[T] as SliceSafeExt<T>>::copy_from_slice_ext",
        "<[T] as SliceSafeExt<T>>::copy_within_ext",
        "<[T] as SliceSafeExt<T>>::swap_with_slice_ext",
        "<[T] as SliceSafeExt<T>>::binary_search_by_ext",
        "<[T] as SliceSafeExt<T>>::partition_dedup_by_ext",
        "<[T] as SliceSafeExt<T>>::get_disjoint_mut_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_mut_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_mut_ext",
        "get_disjoint_check_valid_ext",
        "copy_from_slice_impl",
    ];

    for fn_name in &functions {
        assert_contain(&output, fn_name);
    }

    assert_eq!(
        output.matches("result: SOUND").count(),
        38,
        "expected 38 SOUND results"
    );
}

#[test]
fn std_challenge_18() {
    let output = run_with_args("verify_cases/std-challenge-18", CMD_VERIFY_TARGETED);
    assert!(
        !output.contains("UNSOUND"),
        "unexpected UNSOUND in std-challenge-18"
    );
}

#[test]
fn hashmap() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_TARGETED);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn hashmap_skip_invariant() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn std_challenge_02() {
    let output = run_with_args("verify_cases/std-challenge-02", CMD_VERIFY_TARGETED);

    let functions = [
        "copy_nonoverlapping",
        "copy",
        "swap",
        "swap_nonoverlapping",
        "mem_swap",
        "zeroed",
        "copy_from_slice",
        "size_of_val",
        "align_of_val",
        "min_align_of_val",
    ];

    for fn_name in &functions {
        assert_contain(&output, fn_name);
    }

    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn bump_allocator() {
    let output = run_with_args("verify_cases/bump_allocator", CMD_VERIFY);
    assert_function_result(&output, "BumpAllocator::new", "SOUND");
    assert_function_result(&output, "BumpAllocator::alloc", "SOUND");
    assert_function_result(&output, "BumpAllocator::reset", "SOUND");
}

#[test]
fn free_list_allocator() {
    let output = run_with_args("verify_cases/free_list_allocator", CMD_VERIFY);
    assert_function_result(&output, "FreeListAllocator::new", "SOUND");
    assert_function_result(&output, "FreeListAllocator::alloc", "SOUND");
    assert_unproved_exclusive(&output, "FreeListAllocator::alloc_unsound", &["Align"]);
    assert_function_result(&output, "FreeListAllocator::dealloc", "SOUND");
    assert_function_result(&output, "FreeListAllocator::merge", "SOUND");
}
