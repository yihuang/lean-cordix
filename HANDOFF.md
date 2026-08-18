# Lean-Cordix Faithful Full-Context Model — Handoff

> 本文件是给下一个空白上下文的 agent 的完整接手说明。
> 复制本文件内容给新 agent 即可继续。

## 1. 仓库状态

- 路径：`/Users/huangyi/src/lean-cordix`
- 分支：`faithful-fullctx`
- Toolchain：`leanprover/lean4:v4.34.0-rc1`
- 当前工作区：`LeanCordix/Faithful.lean` 有大量未提交修改；`lean-toolchain` 已更新到 rc1
- Build：`lake build` 通过（38 jobs）
- 工作区不是干净的：有修改未提交

```bash
cd /Users/huangyi/src/lean-cordix
lake build
```

## 2. 项目背景

论文：

> *A Programming Paradigm for Spatiotemporal Composability* — Yifan Shi, Wei Zhang, Tianyi Cui

仓库正在做 faithful 版 full-context 模型的形式化，目标是把之前过度简化的模型替换为符合论文的版本。

核心区别：

- 旧模型 iterator 跑在 `sigmaOf`（active-only）上；
- faithful 模型 iterator 跑在 `FullCtx K V = (ambient, rawSigma)` 上，其中 `rawSigma` 是所有 fiber table 的并集（无论 lifecycle）。

## 3. 关键文件

| 文件 | 内容 |
| --- | --- |
| `LeanCordix/FullCtx.lean` | 底层 `FullCtx K V = CoefCtx K V × CoefCtx K V` |
| `LeanCordix/FullContext.lean` | 旧的全上下文辅助，暂时不核心 |
| `LeanCordix/Faithful.lean` | **当前主战场**：faithful 模型全部定义与定理 |
| `LeanCordix/Independence.lean` | `Iterator.Independent`、`InTransformMonoid`、旧模型 recoverAcc 相关 |
| `cordix.txt` | 论文文本 |

## 4. Faithful 模型核心设计

```lean
abbrev Ctx K V := Full.FullCtx K V
-- = CoefCtx K V × CoefCtx K V

State.fullCtx s := (s.ambient, rawSigma s.reg)
-- rawSigma = 所有 fiber table 的并集，不是 active-only
```

- `Component.iter : Iterator (Ctx K V) E`
- `Lifecycle` accumulator 类型：`Ctx K V → Ctx K V`
- `State.recover s n`：
  - 把 `n.table` 清空；
  - ambient 取 `(κ_n (fullCtx s)).1`。
- `Step.psi`：
  - 对 `lIter / lFinish / lDivertLand`：在目标状态**重新执行** `Iterator.step`，再 `State.writeEffect`；
  - 对 `lUnload`：改为 `State.writeEffect x n (κ (fullCtx x))`（**重要**：不是只取 ambient，否则 independence commutation 不成立）；
  - 其他规则 identity。

## 5. 已经证明的关键定理（均在 `Faithful.lean`）

### 5.1 rawSigma / fullCtx 基础设施

- `rawSigma_cons`
- `rawSigma_del_eq_of_disjoint`
- `rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint`
- `State.fullCtx_of_nodup_of_disjoint`
- `State.writeEffect_preserves_fullCtx_of_confined`

### 5.2 registry / del / set 辅助

- `lookup_eq_of_nodup`
- `lookup_self_of_mem_of_nodup`
- `lookup_some_mem`
- `lookup_none_of_not_mem`
- `lookup_del_self`
- `lookup_del_ne`
- `mem_of_mem_del`
- `mem_map_del`
- `nodupKeys_set`
- `nodupKeys_del`
- `pairwiseDisjointTables_del`
- `key_not_mem_set`
- `mem_of_mem_set_ne`
- `pairwiseDisjointTables_set_of_table_disjoint_from_others`
- `pairwiseDisjointTables_set_empty`
- `pairwiseDisjointTables_set_preserves_table`
- `del_eq_self_of_not_mem`
- `set_set_eq`
- `tableAt_del_ne`

### 5.3 Step.psi 保持

- `Step.psi_preserves_approx`
- `Step.psi_preserves_fullCtx`
- `Step.edit_approx_psi_of_ne_remove`

### 5.4 recovery self-step

- `Step.recover_self_lIter_approx`
- `Step.recover_self_lFinish_approx`
- `Step.recover_self_lDivertLand_approx`
- `Step.recover_self_lUnload_approx`
  - 需要假设 `∀ k ∈ f.comp.prov, (κ (fullCtx s)).2 k = none`（withdrawal）
- `Step.recover_self_oInsert_approx`
- `Step.recover_self_oRetire_approx`
- `Step.recover_self_lBegin_approx`
- `Step.recover_self_lRaise_approx`
- `Step.recover_self_lDivertAbort_approx`
- `Step.recover_self_lLeave_approx`
- `Step.recover_self_approx_of_confined` — 汇总所有非 `O-Remove` self-step；额外接受 `NodupKeys`、`Step.Confined`、`Step.SelfWithdrawsAt`

### 5.5 局部 Thm 61

```lean
theorem State.recover_psi_commute_approx_of_indep
```

### 5.6 NodupKeys / PairwiseDisjointTables 保持

- `State.writeEffect_preserves_nodupKeys`
- `State.writeEffect_preserves_pairwiseDisjointTables`
- `State.recover_preserves_nodupKeys`
- `State.recover_preserves_pairwiseDisjointTables`
- `Step.psi_preserves_nodupKeys`
- `Step.psi_preserves_pairwiseDisjointTables`
- `Step.edit_preserves_nodupKeys`
- `Step.edit_preserves_pairwiseDisjointTables`
- `Step.psiConfinedAt_self_of_confined`
- `Step.psiConfinedAt_self_of_pair_left`
- `Step.psiConfinedAt_self_of_pair_right`
- `Step.next_preserves_nodupKeys`
- `Step.next_preserves_pairwiseDisjointTables`
- `StepTrace.PsiFiberAgrees`
- `StepTrace.PsiConfinedAgrees`
- `Step.psi_preserves_lookup_ne`
- `Step.edit_preserves_lookup_ne`
- `StepTrace.NoNonNInsert`
- `SameFiberAt`
- `sameFiber_eq_sameFiberAt`
- `sameFiberAt_comm`
- `set_preserves_sameFiberAt`
- `set_preserves_sameFiberAt_of_prov`
- `State.writeEffect_preserves_sameFiberAt`
- `State.writeEffect_preserves_sameFiberAt_left/right`
- `Step.psi_preserves_sameFiberAt`
- `Step.edit_preserves_sameFiberAt`
- `Step.edit_preserves_sameFiberAt_self_of_not_insert_remove`
- `sameFiberAt_trans`
- `StepTrace.PsiFiberAgrees_of_sameFiberAt`
- `StepTrace.recovery_exactness_cor62_fiber_stable`

### 5.6.1 新增 write-confinement 接口（用于消去 `PsiConfinedAgrees`）

- `ConfinedIterator ι P`：iterator 的 write half，所有成功 step 在 `P` 外保持 sigma 不变
- `ConfinedAcc κ P`：accumulator 的 write half
- `Component.Confined`
- `Lifecycle.Confined`
- `confinedEffect_of_confinedIterator`
- `confinedEffect_of_confinedAcc`
- `recover_preserves_confined_disjoint`
- `confinedEffect_transfer_of_approx`
- `confinedEffect_of_confinedIterator_of_recover`
- `confinedEffect_of_confinedAcc_of_recover`
- `Step.psiConfinedAt_of_confined`
- `StepTrace.PsiConfinedAgrees_of_confined`

这些是 8.2 实例化所需的保持定理；`Step.next_*` 组合了 `edit ∘ psi`。

### 5.7 Trace-level Thm 61 / Cor 62（已编译，带全称 side conditions）

```lean
theorem StepTrace.recovery_exactness_aux
theorem StepTrace.recovery_exactness_recoverAcc
theorem StepTrace.recovery_exactness_cor62
theorem StepTrace.recovery_exactness_cor62_wellformed
theorem StepTrace.recovery_exactness_cor62_fiber_stable
theorem StepTrace.recovery_exactness_cor62_confined
```

`recovery_exactness_cor62_wellformed` 是方便形式：在全局 `NodupKeys` /
`PairwiseDisjointTables` 假设下，用 `State.recover_preserves_*` 自动消去
`hnrec/hnx/hdisjrec/hdisjx` 四个冗余参数。

`recovery_exactness_aux` / `recovery_exactness_recoverAcc` 现在要求 `hself` 只给 `≈`（不需要 fullCtx 等式），`hcomm` 也只给 `≈`；fullCtx 等式由 `hnrec/hnx/hdisjrec/hdisjx` 通过 `State.fullCtx_of_nodup_of_disjoint` 推导。`hself` 还要求 `st.kind ≠ oRemove`（因为 trace 本身排除 `O-Remove`）。`hedit` 是 `≈` 版本，由 `State.recover_next_approx_recover_psi_of_ne_remove` 提供。

`recovery_exactness_aux` 已改为只要求当前 folded state `x` 的局部 `NodupKeys x.reg` / `PairwiseDisjointTables x.reg`，不再要求全称 `hnx/hdisjx`；归纳推进时用 `Step.psi_preserves_nodupKeys` / `Step.psi_preserves_pairwiseDisjointTables` 和 `PsiConfinedAt` self-pair helper 自动保持。`recovery_exactness_recoverAcc` / `recovery_exactness_cor62` 也改为只要求初始 `s` 的局部 `NodupKeys s.reg` / `PairwiseDisjointTables s.reg`。

`SameFiber` / `PsiConfinedAt` 的全称 side conditions 也已改为 trace-local 谓词 `PsiFiberAgrees` / `PsiConfinedAgrees`，它们沿着 `foldPsiExcept` 的折叠路径递归给出每个非 `n` 步所需的 fiber 一致性和 confined-at 条件。

这两个定理使用全称量化的 side conditions：

- `SamePresence`
- `SameProvision`
- `NodupKeys`
- `PairwiseDisjointTables`
- `Step.PsiConfinedAt`

`recovery_exactness_cor62` 是 Cor 62 的 faithful 形式：在 `iterOf`/independence/withdraw/confined/nodup/disjoint 等全称假设下直接调用 `recovery_exactness_recoverAcc`。

## 6. 重要概念与定义

### 6.1 `PairwiseDisjointTables`

```lean
def PairwiseDisjointTables (r : Registry N K V E) : Prop :=
  ∀ p ∈ r, ∀ q ∈ r, p.1 ≠ q.1 →
    ∀ k, p.2.table k = none ∨ q.2.table k = none
```

这是论文 well-formedness 第 2 条（不同 fiber provision 不相交）在 table 层面的体现。

### 6.2 `Step.PsiConfinedAt`

```lean
def Step.PsiConfinedAt (st : Step s) (x y : State N K E V) : Prop
```

- `lIter/lFinish/lDivertLand`：重算出的同一个 `δ'` 在 `x`、`y` 上都 `ConfinedEffect`；
- `lUnload`：`κ (fullCtx x)` 与 `κ (fullCtx y)` 分别 confined；
- 其他为 `True`。

### 6.3 `Step.SelfWithdrawsAt`

```lean
def Step.SelfWithdrawsAt (st : Step s) : Prop :=
  match st with
  | lUnload n f κ v o hf hl hg =>
      ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none
  | _ => True
```

这是 `L-Unload` self-step 的 withdrawal 条件；其他 self-step 自动为 `True`。

### 6.4 `SamePresence` / `SameProvision` / `SameFiber`

```lean
def SamePresence s n st x : Prop :=
  (lookup (State.recover s n).reg st.name).isSome ↔ (lookup x.reg st.name).isSome

def SameProvision s n st x : Prop :=
  ∀ gx gy, lookup (State.recover s n).reg st.name = some gx →
    lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov

def SameFiber s n st x : Prop :=
  match lookup (State.recover s n).reg st.name, lookup x.reg st.name with
  | some gx, some gy => gx.comp.prov = gy.comp.prov
  | none, none => True
  | _, _ => False
```

`SameFiber` 是 `SamePresence` + `SameProvision` 的合并版本；
`samePresence_of_sameFiber` / `sameProvision_of_sameFiber` /
`sameFiber_of_samePresence_sameProvision` 提供双向转换。

`SamePresence` / `SameProvision` wrapper 是为了绕开 Lean 的一个 elaboration bug：
**局部函数直接返回 `Iff` 时，应用会报 `Function expected`**。
用 wrapper 后，需要 `Iff` 时再 `simpa [SamePresence]`。

## 7. 踩过的坑

1. **`rawSigma_del_eq` 没有 disjointness 是假的**
   - 因为 `rawSigma` 是左偏 `Option.or`，顺序敏感；
   - 反例：两个 registry 顺序不同但 tableAt 相同，rawSigma 不同；
   - 所以必须加 `PairwiseDisjointTables`。
2. **`<|>` 优先级低于 `=`**
   - 写 `a = b <|> c` 会解析成 `(a = b) <|> c`；
   - 必须写 `a = (b <|> c)`。
3. **Lean 局部函数返回 `Iff` 的 elaboration 问题**
   - 用 `SamePresence` / `SameProvision` wrapper 绕过。
4. **`L-Unload` 的 `Step.psi` 必须写完整 `writeEffect`**
   - 如果只取 ambient，`Iterator.Independent.comm` 无法用于 lUnload。
5. **`induction ht generalizing x` 时，side conditions 必须全称量化 over x**
   - 否则 IH 无法从 `x` 推进到 `Step.psi st x`。
6. **toolchain 不是问题**
   - 已更新到 v4.34.0-rc1 复现同样问题，确认是 Lean elaboration 行为。
7. **`L-Begin` 需要空表前提**
   - `recover` 对 `inactive` 不自动清表，所以 faithful 的 `Step.lBegin` 增加了 `htable : f.table = fun _ => none`，否则 self-step recovery 不成立。
8. **`recover` 对 `edit` 的 commutation 只能到 `≈`，不能到 `=`**
   - 当 `n` 不存在/`inactive` 时 `recover` 返回整个状态，因此 `hedit` 使用 `State.recover_next_approx_recover_psi_of_ne_remove`（`≈`），而不是状态等式。

## 8. 尚未完成 / 下一步

### 8.1 Cor 62（terminal recovery）— 已搭好框架

已完成：

1. 所有非 `O-Remove` self-step 的 `≈` 不变性已补齐（`Step.recover_self_approx_of_confined`）。
   - 为此给 `Step.lBegin` 增加了 `htable : f.table = fun _ => none` 前提（只影响 `Faithful.lean`）。
2. 已实现 `StepTrace.recovery_exactness_cor62`：在 independence / withdraw / confined / nodup / disjoint 等全称假设下调用 `recovery_exactness_recoverAcc`。
3. 已证明 `NodupKeys` / `PairwiseDisjointTables` 在 `Step.psi`、`Step.edit`、`Step.next`、`State.recover` 下的保持（见 5.6）。
4. 已把 `recovery_exactness_aux` / `recoverAcc` / `cor62` 中全称 `hnx/hdisjx` 改为局部初始假设，并用保持定理在归纳中自动推进。
5. 已增加 `StepTrace.recovery_exactness_cor62_wellformed`，用全局 well-formedness 消去 `hnrec/hnx/hdisjrec/hdisjx`；并把 `SamePresence` / `SameProvision` 合并为 `SameFiber`。
6. 已把 `SameFiber` / `PsiConfinedAt` 的全称 side conditions 改为 trace-local 的 `PsiFiberAgrees` / `PsiConfinedAgrees`，沿着 `foldPsiExcept` 递归携带。
7. 已从 primitive trace 不变量推导这两个 trace 谓词：`PsiFiberAgrees_of_sameFiberAt` 与 `PsiConfinedAgrees_of_confined`（后者需要新增的 write-confinement 接口，见 5.6.1）。

### 8.2 具体实例化 trace-level Thm 61 / Cor 62

现在已从 well-formedness + independence / trace 不变量推导：

- ✅ `PsiFiberAgrees`：由 `PsiFiberAgrees_of_sameFiberAt` 从 `SameFiberAt` + `NoNonNInsert` + `hno_remove` 推出
- ✅ `PsiConfinedAgrees`：由 `PsiConfinedAgrees_of_confined` 从 write-confined iterators/accumulators + `SameFiberAt` + `NoNonNInsert` + `hno_remove` + recovery `≈` invariants 推出
- ✅ `recovery_exactness_cor62_confined`：在 `cor62_fiber_stable` 的基础上额外接受 `hconf_iter` / `hconf_acc`，自动导出 `hconf_trace`

`NodupKeys` / `PairwiseDisjointTables` 相关 side conditions 已通过保持定理和 `cor62_wellformed` 消去；`SamePresence` / `SameProvision` 已合并为 `SameFiber`，并打包进 `PsiFiberAgrees`。

当前仍可选的后续工作：

- 把 `hconf_iter` / `hconf_acc` 从更 primitive 的 `Component.Confined` / `Lifecycle.Confined` 与保持定理推出；
- 或把 `ConfinedWellFormed` / `TableConfinedWellFormed` 的保持定理迁移到 faithful 模型；
- 用 `ConfinedEffect` + provision 不相交来推出 `SameProvision`（已由 `SameFiberAt` 路线覆盖，也可再整理）。

### 8.3 模块转正

已完成：

- 删除 `Faithful.lean` 的 `parallel development` 注释，改为 canonical full-context model；
- 在 `LeanCordix.lean` 根注释中标注 `Faithful` 为 canonical 模型，旧模块作为 legacy dependencies 保留；
- 更新 README：新增 `LeanCordix.Faithful` 条目、Scope 条目，并更新 future work 说明。

决定：暂不删除旧 `FullCalculus` / `Global` / `Independence`，因为 `Faithful` 仍复用 `Full.StepKind`、iterator independence 等基础设施；后续若把公共基础设施抽离，可以再清理 legacy 模块。

## 9. 推荐的继续顺序

1. ✅ 补 self-step 覆盖（含 `lBegin/lRaise/lDivertAbort/lLeave/oRetire`）并构造 `Step.recover_self_approx_of_confined`；
2. ✅ 构造 Cor 62 的 `hself` / `hcomm` / `hedit` 并实现 `StepTrace.recovery_exactness_cor62`；
3. ✅ 证明 `NodupKeys` / `PairwiseDisjointTables` 在 `Step.psi` / `Step.edit` 下保持（并补了 `Step.next` / `State.recover` 版本）；
4. ✅ 已把保持定理接入 folded-state 的 `NodupKeys` / `PairwiseDisjointTables` 推进；并完成 `PsiConfinedAgrees` 的实例化（新增 write-confinement 接口）；
5. 最后做模块整合和文档更新。

## 10. 验证命令

```bash
cd /Users/huangyi/src/lean-cordix
lake build
```

当前 build 绿色。
