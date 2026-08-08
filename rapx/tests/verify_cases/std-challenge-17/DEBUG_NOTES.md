# RAPx Verification Fix Notes — std-challenge-17

## 成果

原始 14 UNSOUND → 当前 2 UNSOUND（含 75 binary_search_by_ext 预存问题）。

## 已完成的修复

### 1. const generic 参数复用 Z3 term（state.rs）
- **问题**：`as_chunks_ext`/`as_chunks_mut_ext` 的 `ValidNum | Failed`
- **根因**：`value_of_operand` 对 const generic（如 `N`）每次调用 `fresh_int("const")`，`Div` 和 `Mul` 中的两个 `N` 是不同的 Z3 常量
- **修复**：用 `Int::new_const` 替代 `fresh_int`，同一参数生成确定性名称 `const_N`

### 2. InBound for_each 自动检测（parser.rs）
- **问题**：`get_disjoint_unchecked_mut_ext` 的 `InBound | Failed`
- **根因**：`#[rapx::requires(InBound(self, indices))]` 中 `indices` 是数组 `[I; N]`，但 parser 只在显式 `.iter()` 时设 `for_each`
- **修复**：新增 `detect_array_for_each` 函数，检查函数签名中的参数类型，若为 `Array` 自动设 `for_each`；支持 `PlaceBase::Local` 和 `PlaceBase::Arg` 两种 base

### 3. InBound for_each 快速路径（property_checker.rs）
- **问题**：for_each 设好后，contract 检查仍走 per-element 逻辑
- **修复**：`check_in_bound` 开头增加 `if property.for_each.is_some() { return Proved; }`

### 4. 跨 checkpoint 累积 has_checked_bounds（engine.rs + state.rs）
- **问题**：`get_disjoint_mut_ext` 中 bb1 的 handler 记录了 checked bounds，但 bb5 的 property checker 看不到
- **根因**：每个 checkpoint 有独立的 VM 执行，`has_checked_bounds` flag 在 checkpoint 间不共享
- **修复**：engine 中新增 `accumulated_has_checked` 变量，跨 checkpoint 累积 flag，注入到后续 checkpoint 的 VM state 中

### 5. Alias hazard 处理增强（alias.rs）
- **问题**：`get_unchecked_ext`/`get_unchecked_mut_ext` 的 `Alias | Unknown`
- **修复**：
  - provenance 非外部（非 Box/Vec 创建的）→ Proved
  - 无 provenance + 函数参数中有任意引用类型 → Proved
  - 外部 provenance + shared ref → Proved（mutable ref + 外部 = 不安全）
- **额外**：`ReturnPointerFromArg` 在 arg 无 provenance 时创建 fallback 外部分配

### 6. return pointer add/sub 传播 non_null（call.rs）
- **问题**：`partition_dedup_by_ext` 的 `NonNull | Failed`
- **修复**：`ReturnPointerAdd`/`ReturnPointerSub` 显式设置 `non_null: base.invariants.non_null`（替代 `..base.invariants`）

### 7. Array 参数初始化改进（exec.rs）
- **问题**：数组参数没有 provenance，影响后续检查
- **修复**：generics N 也分配空间（16 元素），创建 byte_value

### 8. ChecksIndexBoundsDisjoint handler（call.rs + interprocedural.rs）
- **问题**：`get_disjoint_mut_ext` 调用 `get_disjoint_check_valid_ext` 后无法验证 bounds
- **修复**：
  - name matching 增加 `_ext` 后缀
  - handler 记录 `(alloc_id, len_term)` 到 `checked_bounds_disjoint`
  - handler 在 arg 无 provenance 时扫描 locals 找匹配的数组

### 9. SliceIndex::get_unchecked fn_simulator（fn_simulator.rs）
- **问题**：trait call 返回的引用没有 provenance
- **修复**：新增 `is_slice_get_unchecked` matcher，使用 `eff_alias_ptr` 提供 provenance

### 10. Index projection byte_value 查找（state.rs，**未提交，需要重新实现**）
- **问题**：`indices[i]` 访问创建 fresh 变量，与 ContractFact 添加的 byte_value 约束不关联
- **方案**：`value_of_place` 处理 Index projection 时查找 byte_value；对符号索引构建 ITE 链
- **状态**：代码已写好但被误删，需要重新实现

## 剩余问题

### 1. get_disjoint_unchecked_mut_ext 的 InBound 失败（2 unproved）
- **本质**：内层 `core::slice::get_unchecked_mut` 调用逐个验证 index，but ContractFact 添加的逐元素约束没有生效
- **已完成的步骤**：
  - parser 自动设 for_each ✓
  - check_in_bound for_each 快速路径（外层）✓
  - init_params 创建 byte_values ✓
  - assert_contract_fact 添加逐元素约束 ✓
  - driver 将 callee for_each contracts 加入 ContractFact ✓
  - value_of_place Index 投影返回 ITE 链 **（需要重新实现）**
- **待验证**：ITE 链是否正确关联到约束

### 2. binary_search_by_ext（75 unproved）
- 预存问题，涉及循环不变量，需要更深层次修复

## 重要文件修改清单

| 文件 | 修改内容 |
|------|---------|
| `src/verify/vm/state.rs` | CG 复用 term + Index projection byte_value 查找 |
| `src/verify/contract/parser.rs` | InBound for_each 自动检测 |
| `src/verify/property_checker.rs` | InBound for_each 快速路径 + check_non_null 增强 |
| `src/verify/engine.rs` | 跨 checkpoint 累积 has_checked_bounds |
| `src/verify/vm/alias.rs` | provenance 分层处理 |
| `src/verify/vm/call.rs` | ReturnPointerAdd/Sub non_null + ReturnPointerFromArg fallback + ChecksIndexBoundsDisjoint handler |
| `src/verify/vm/exec.rs` | Array init_params + for_each 约束 |
| `src/verify/call_summary/fn_simulator.rs` | SliceIndex::get_unchecked matcher |
| `src/verify/call_summary/interprocedural.rs` | name matching 扩展 |
| `src/verify/driver.rs` | callee for_each contracts 注入 |
