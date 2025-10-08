use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Terminator, TerminatorKind, Operand};
use rustc_middle::ty::{TyCtxt, InstanceDef};
use std::collections::HashSet;

// 修改返回值类型为调用链的向量
pub fn get_all_std_unsafe_chains(tcx: TyCtxt, def_id: DefId) -> Vec<Vec<String>> {
    let mut results = Vec::new();
    let mut visited = HashSet::new(); // 避免循环调用
    let mut current_chain = Vec::new();
    
    // 开始DFS遍历
    dfs_find_unsafe_chains(tcx, def_id, &mut current_chain, &mut results, &mut visited);
    results
}

// DFS递归查找unsafe调用链
fn dfs_find_unsafe_chains(
    tcx: TyCtxt,
    def_id: DefId,
    current_chain: &mut Vec<String>,
    results: &mut Vec<Vec<String>>,
    visited: &mut HashSet<DefId>,
) {
    // 避免循环调用
    if visited.contains(&def_id) {
        return;
    }
    visited.insert(def_id);
    
    let current_func_name = get_cleaned_def_path_name(tcx, def_id);
    current_chain.push(current_func_name.clone());
    
    // 获取当前函数的所有unsafe callee
    let unsafe_callees = find_unsafe_callees_in_function(tcx, def_id);
    
    if unsafe_callees.is_empty() {
        // 如果没有更多的unsafe callee，保存当前链
        results.push(current_chain.clone());
    } else {
        // 对每个unsafe callee继续DFS
        for (callee_def_id, callee_name) in unsafe_callees {
            dfs_find_unsafe_chains(tcx, callee_def_id, current_chain, results, visited);
        }
    }
    
    // 回溯
    current_chain.pop();
    visited.remove(&def_id);
}

// 在函数中查找所有unsafe callee
fn find_unsafe_callees_in_function(tcx: TyCtxt, def_id: DefId) -> Vec<(DefId, String)> {
    let mut callees = Vec::new();
    
    if let Some(body) = try_get_mir(tcx, def_id) {
        for bb in body.basic_blocks.iter() {
            if let Some(terminator) = &bb.terminator {
                if let Some((callee_def_id, callee_name)) = extract_unsafe_callee(tcx, terminator) {
                    callees.push((callee_def_id, callee_name));
                }
            }
        }
    }
    
    callees
}

// 从terminator中提取unsafe callee
fn extract_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Option<(DefId, String)> {
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Operand::Constant(func_constant) = func {
            if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                // 检查被调用函数是否是unsafe的
                if !check_safety(tcx, *callee_def_id) {
                    let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
                    return Some((*callee_def_id, func_name));
                }
            }
        }
    }
    None
}

// 安全地获取MIR，处理可能无法获取MIR的情况
fn try_get_mir(tcx: TyCtxt, def_id: DefId) -> Option<&rustc_middle::mir::Body<'_>> {
    // 这里可能需要根据实际情况调整，有些def_id可能没有MIR
    if tcx.is_mir_available(def_id) {
        Some(tcx.optimized_mir(def_id))
    } else {
        None
    }
}

// 清理def path名称的辅助函数
fn get_cleaned_def_path_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    // 这里实现你的路径清理逻辑
    tcx.def_path_str(def_id)
}

// 打印调用链的函数
pub fn print_unsafe_chains(chains: &[Vec<String>]) {
    if chains.is_empty() {
        println!("No unsafe call chains found.");
        return;
    }
    
    println!("Found {} unsafe call chain(s):", chains.len());
    for (i, chain) in chains.iter().enumerate() {
        println!("Chain {}:", i + 1);
        for (j, func_name) in chain.iter().enumerate() {
            let indent = "  ".repeat(j);
            println!("{}{}-> {}", indent, if j > 0 { " " } else { "" }, func_name);
        }
        println!();
    }
}

// 使用示例
pub fn analyze_and_print_unsafe_chains(tcx: TyCtxt, def_id: DefId) {
    let chains = get_all_std_unsafe_chains(tcx, def_id);
    print_unsafe_chains(&chains);
}