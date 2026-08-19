# Lean-Cordix Full-Context Model — Design Notes

This document describes the Lean formalization in `LeanCordix/`: core
definitions, module layout, proof architecture, theorem dependencies, and
the correspondence to the paper *A Programming Paradigm for
Spatiotemporal Composability*.

## 1. Overview

The current implementation formalizes the full-context model of the paper.
Effect iterators run against the complete context

```lean
abbrev Ctx K V := Full.FullCtx K V
-- FullCtx K V = CoefCtx K V × CoefCtx K V
--             = (ambient, sigma)
```

where `sigma` is the union of **all** fiber tables, regardless of lifecycle:

```lean
State.fullCtx s := (s.ambient, rawSigma s.reg)
```

`rawSigma` uses left-biased `Option.or` (`<|>`), so it is order-sensitive.
The structural theorems about splitting `rawSigma` therefore require
`PairwiseDisjointTables`, which says that two distinct fibers never define
the same key.

## 2. Module Layout

The model is split into flat modules under `LeanCordix/`:

| Module | Content |
| --- | --- |
| `LeanCordix/Basic.lean` | Core definitions and infrastructure: `Ctx`, `Component`, `Lifecycle`, `Fiber`, `Registry`, `State`, `lookup`/`set`/`del`, `NodupKeys`, `PairwiseDisjointTables`, `sigmaOf`/`rawSigma`, `State.recover`/`writeEffect`, write-confinement, `SameFiberAt` |
| `LeanCordix/Step.lean` | `Step` records, `Step.psi`/`Step.edit`/`Step.next`, `Step.factorization`, `Step.Confined`/`Step.PsiConfinedAt`, and local preservation lemmas for `psi`/`edit`/`next` |
| `LeanCordix/Approx.lean` | `State.Approx` (`≈`), rawSigma splitting/merging theorems, `State.recover_psi_commute_approx_of_indep` (local Theorem 61) |
| `LeanCordix/Recovery.lean` | Confinement transfer, `Step.psi_preserves_approx`/`fullCtx`, `edit_approx_psi_of_ne_remove`, self-step recovery lemmas, `SameFiber` |
| `LeanCordix/Trace.lean` | `StepTrace`, `foldPsiExcept`, trace-local predicates `PsiFiberAgrees`/`PsiConfinedAgrees`, trace-level Theorem 61 / Corollary 62 |
| `LeanCordix/WellFormed.lean` | Definition 58 well-formedness and Theorem 59 preservation, including `WellFormed.preserved` and trace preservation |
| `LeanCordix/Progress.lean` | Theorem 66 progress/no-deadlock scaffolding: `Precedes`, `Acyclic`, `ConfinedWellFormed`, `exists_lifecycle_step_of_not_quiet` |
| `LeanCordix/Termination.lean` | Theorem 66 termination scaffolding: `StepTrace.length`, `countFor`, `targetTurns`, interval bounds |
| `LeanCordix/Vestigial.lean` | Lemma 54/57 vestigial entries and step-local preservation lemmas |
| `LeanCordix/Invariance.lean` | Lemma 55 observational state equivalence and `step_transport` |
| `LeanCordix/Equivariance.lean` | Lemma 56 name renaming/equivariance: `NameEquiv`, `Rename`, `step_rename`, `step_rename_bwd`, `step_rename_next` |
| `LeanCordix/Coherence.lean` | Theorem 64 resolution coherence |
| `LeanCordix/TableConfined.lean` | Table-confinement machinery, `Registry.TableConfined`, `TableConfinedWellFormed`, table-aware trace preservation |
| `LeanCordix/Confluence.lean` | Theorem 73 scaffolding: support/totality definitions, Lemma 68/70/71 statements, and a proved O-Remove/O-Remove transposition special case |

Shared infrastructure:

- `LeanCordix/FullCtx.lean` — the `FullCtx` type;
- `LeanCordix/Iterator.lean` — `Iterator`, `Reachable`, `WitnessedAll`, and the generic `Iterator.InTransformMonoid` / `Iterator.Independent` / `Iterator.PairwiseIndependent`;
- `LeanCordix/StepKind.lean` — the ten rule kinds (`Full.StepKind`).

## 3. Core Definitions

### 3.1 Component, Lifecycle, Fiber, Registry

```lean
structure Component (K V E) where
  spec : Spec K
  prov : List K
  iter : Iterator (Ctx K V) E
  wit  : Iterator.WitnessedAll iter
```

`Lifecycle` is the four-state lifecycle:

```lean
inductive Lifecycle N K V E
  | inactive (outcome : Option E)
  | loading (iter : Iterator (Ctx K V) E) (acc : Ctx K V → Ctx K V)
      (view : K → Option N)
  | active (acc : Ctx K V → Ctx K V) (view : K → Option N)
  | unloading (acc : Ctx K V → Ctx K V) (view : K → Option N)
      (outcome : Option E)
```

`Fiber` consists of a `Component`, a parent, a table, a retired flag, and a
lifecycle. `Registry` is `List (N × Fiber N K V E)`. Updates use `set` as a
pointwise update that replaces the first matching name, which helps preserve
`NodupKeys`.

### 3.2 `rawSigma` and Well-Formedness

```lean
def rawSigma (r : Registry N K V E) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc => p.2.table k <|> acc
```

`PairwiseDisjointTables` requires that two distinct fibers never have
non-`none` tables at the same key:

```lean
def PairwiseDisjointTables (r : Registry N K V E) : Prop :=
  ∀ p ∈ r, ∀ q ∈ r, p.1 ≠ q.1 →
    ∀ k, p.2.table k = none ∨ q.2.table k = none
```

`NodupKeys` says the registry has no duplicate keys. These two conditions are
prerequisites for many rawSigma structure theorems.

### 3.3 `State`, `recover`, `writeEffect`

```lean
structure State N K E V where
  reg     : Registry N K V E
  ambient : CoefCtx K V

def State.fullCtx s := (s.ambient, rawSigma s.reg)
```

- `State.recover s n` finds the fiber at `n`, clears its `table`, and sets
  the ambient to `(κ_n (fullCtx s)).1`. If `n` is absent or inactive, it
  returns the original state.
- `State.writeEffect x n δ` writes `δ.2` into `n.table` split by `n.prov`
  and sets the ambient to `δ.1`.
- `State.Withdraws s n` states
  `fullCtx (recover s n) = accAt s n (fullCtx s)`, the state-level condition
  corresponding to Eq. (56).

### 3.4 `Step` and Eq. (52)

`Step s` is a type-level step record with an extractable rule kind:

```lean
def Step.name : Step s → N
def Step.kind : Step s → Full.StepKind
```

The state map `Step.psi` is designed as follows:

- `lIter` / `lFinish` / `lDivertLand` re-run
  `Iterator.step ι (State.fullCtx x)` on the target state `x`, then apply
  `State.writeEffect x n δ'`;
- `lUnload` applies `State.writeEffect x n (κ (fullCtx x))` on the target
  state, using the full context rather than only the ambient part;
- all other rules are the identity.

`Step.edit` only changes control fields. Therefore:

```lean
def Step.next st := edit st (psi st s)

theorem Step.factorization (st : Step s) : next st = edit st (psi st s) := rfl
```

This is Eq. (52): `s' = edit (Ψ s)`.

### 3.5 `≈` (`State.Approx`)

```lean
structure State.Approx (s s' : State N K E V) : Prop where
  ambient : s.ambient = s'.ambient
  tables  : ∀ n, State.tableAt s n = State.tableAt s' n
```

`≈` ignores control fields and compares only the ambient context and every
name's table. It is an equivalence relation. Under `NodupKeys` and
`PairwiseDisjointTables`, `≈` can be upgraded to `fullCtx` equality:

```lean
theorem State.fullCtx_of_nodup_of_disjoint
    (hs ht : NodupKeys ...) (hdisjs hdisjt : PairwiseDisjointTables ...)
    (h : State.Approx s t) : State.fullCtx s = State.fullCtx t
```

### 3.6 Write-Confinement

```lean
def ConfinedIterator ι P :=
  ∀ γ, match Iterator.step ι γ with
    | .ok (δ, _, _) => ∀ k, k ∉ P → γ.2 k = δ.2 k
    | .error _ => True

def ConfinedAcc κ P :=
  ∀ γ k, k ∉ P → γ.2 k = (κ γ).2 k
```

`Component.Confined` and `Lifecycle.Confined` package the write half of
iterators and accumulators. `Step.Confined` is the single-step confinement at
the source state; `Step.PsiConfinedAt` is the pair version needed when
`Step.psi` is re-evaluated on arbitrary states.

### 3.7 Traces

```lean
inductive StepTrace : State N K E V → State N K E V → Type
  | nil (s) : StepTrace s s
  | cons {s₁ s₂ s₃} (st : Step s₁) (hnext : Step.next st = s₂)
      (ht : StepTrace s₂ s₃) : StepTrace s₁ s₃
```

- `foldPsi` folds `Step.psi` over a trace;
- `foldPsiExcept n` skips all steps acting on `n`;
- `NoNonNInsert n` says no step other than `n` performs `oInsert`;
- `PsiFiberAgrees n x ht` recursively requires `SameFiber` for every non-`n`
  step along the `foldPsiExcept` path;
- `PsiConfinedAgrees n x ht` recursively requires `Step.PsiConfinedAt` for
  every non-`n` step along the same path.

## 4. Proof Architecture

The proof is organized in five layers:

```
Basic registry/rawSigma theorems
        ↓
Step local preservation lemmas
        ↓
≈ and local Theorem 61
        ↓
self-step recovery / SameFiber / confinement transfer
        ↓
trace-level Theorem 61 / Corollary 62
```

### 4.1 Layer 1: Registry and rawSigma Infrastructure

`Basic.lean` and `Approx.lean` contain:

- `lookup`/`set`/`del` properties:
  `lookup_set_eq`, `lookup_set_ne`, `lookup_del_self`, `lookup_del_ne`,
  `lookup_none_of_not_mem`, `lookup_some_mem`,
  `lookup_self_of_mem_of_nodup`;
- well-formedness preservation:
  `nodupKeys_set`, `nodupKeys_del`, `pairwiseDisjointTables_del`,
  `pairwiseDisjointTables_set_of_table_disjoint_from_others`,
  `pairwiseDisjointTables_set_empty`,
  `pairwiseDisjointTables_set_preserves_table`;
- rawSigma structure:
  `rawSigma_cons`, `rawSigma_del_eq_of_disjoint`,
  `rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint`;
- key consequences:
  `State.fullCtx_of_nodup_of_disjoint`,
  `State.writeEffect_preserves_fullCtx_of_confined`.

The goal is to make the order-sensitive `rawSigma` well-behaved under the
well-formedness conditions, so that `≈` can later be upgraded to `fullCtx`
equality.

### 4.2 Layer 2: Local Preservation by `Step.psi` / `Step.edit`

`Step.lean` proves that `psi` and `edit` preserve:

- `NodupKeys`:
  `Step.psi_preserves_nodupKeys`, `Step.edit_preserves_nodupKeys`;
- `PairwiseDisjointTables`:
  `Step.psi_preserves_pairwiseDisjointTables`,
  `Step.edit_preserves_pairwiseDisjointTables`;
- lookups at other names:
  `Step.psi_preserves_lookup_ne`, `Step.edit_preserves_lookup_ne`;
- pointwise fiber agreement:
  `Step.psi_preserves_sameFiberAt`, `Step.edit_preserves_sameFiberAt`.

It also proves the self-pair helpers for `PsiConfinedAt`:

- `Step.psiConfinedAt_self_of_confined`;
- `Step.psiConfinedAt_self_of_pair_left` / `_pair_right`.

These are essential for pushing `NodupKeys` / `PairwiseDisjointTables` from
`x` to `Step.psi st x` during trace induction.

### 4.3 Layer 3: `≈` and Local Theorem 61

The central theorem in `Approx.lean` is the local form of Theorem 61:

```lean
theorem State.recover_psi_commute_approx_of_indep
    {s : State N K E V} (st : Step s) {n : N}
    (hne : n ≠ st.name)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : Iterator.Independent (iterOf n) (iterOf st.name))
    (hn_mem : Iterator.InTransformMonoid (iterOf n) (State.accAt s n))
    (hm_mem : ...) :
    State.Approx (State.recover (Step.psi st s) n)
      (Step.psi st (State.recover s n))
```

It says that if the accumulator at `n` and the iterator of another fiber
satisfy the independence condition of Definition 60, then `recover n`
commutes with that fiber's `psi` up to `≈`. The `lUnload` case uses the full
`writeEffect` precisely because the accumulator commutation must be applied
to the whole `fullCtx`.

### 4.4 Layer 4: Self-Step Recovery and Side Conditions

`Recovery.lean` proves that every non-`O-Remove` self-step is invisible to
`recover n` up to `≈`:

```lean
theorem Step.recover_self_lIter_approx
theorem Step.recover_self_lFinish_approx
theorem Step.recover_self_lDivertLand_approx
theorem Step.recover_self_lUnload_approx
theorem Step.recover_self_oInsert_approx
theorem Step.recover_self_lBegin_approx
theorem Step.recover_self_lRaise_approx
theorem Step.recover_self_lDivertAbort_approx
theorem Step.recover_self_lLeave_approx
theorem Step.recover_self_oRetire_approx
```

These are combined into:

```lean
theorem Step.recover_self_approx_of_confined
```

`Recovery.lean` also defines:

- `Step.SelfWithdrawsAt`: the withdrawal condition needed by `lUnload`;
- `SamePresence` / `SameProvision` / `SameFiber`: presence and provision
  agreement for the fiber acted on by a step;
- `sameFiber_eq_sameFiberAt`: connects `SameFiber` to `SameFiberAt`.

Additional preservation theorems include:

```lean
theorem Step.psiConfinedAt_of_confined
theorem Step.psi_preserves_approx
theorem Step.psi_preserves_fullCtx
theorem Step.edit_approx_psi_of_ne_remove
theorem State.recover_next_approx_recover_psi_of_ne_remove
```

`Step.edit_approx_psi_of_ne_remove` is the `≈`-level form of Eq. (52): for
non-`O-Remove` steps, `edit` does not change `≈`.

### 4.5 Layer 5: Trace-Level Theorem 61 / Corollary 62

`Trace.lean` first makes the side conditions trace-local, so induction can
advance from `x` to `Step.psi st x`:

```lean
def PsiFiberAgrees n x ht
def PsiConfinedAgrees n x ht
```

Then it proves two derived theorems:

```lean
theorem PsiFiberAgrees_of_sameFiberAt
theorem PsiConfinedAgrees_of_confined
```

The first derives `PsiFiberAgrees` from `SameFiberAt`, `NoNonNInsert`, and
`hno_remove`. The second derives `PsiConfinedAgrees` from write-confined
iterators/accumulators and the recovery `≈` invariants.

The main theorem chain is:

```lean
theorem recovery_exactness_aux
theorem recovery_exactness_recoverAcc
theorem recovery_exactness_cor62
theorem recovery_exactness_cor62_wellformed
theorem recovery_exactness_cor62_fiber_stable
theorem recovery_exactness_cor62_confined
```

- `recovery_exactness_aux` is the induction engine over `foldPsiExcept`;
- `recovery_exactness_recoverAcc` turns `hstart` and the independence
  assumptions into `hself` / `hcomm` / `hedit`;
- `recovery_exactness_cor62` is the trace-level Corollary 62 form;
- `recovery_exactness_cor62_wellformed` uses global `NodupKeys` /
  `PairwiseDisjointTables` to eliminate redundant parameters;
- `recovery_exactness_cor62_fiber_stable` and `_confined` derive
  `PsiFiberAgrees` / `PsiConfinedAgrees` from primitive trace invariants.

## 5. Theorem Dependencies

The main dependency direction is:

```text
Basic registry lemmas
        │
        ▼
rawSigma splitting / fullCtx equivalence
        │
        ▼
Step.psi/edit preservation
        │
        ▼
Step.psi_preserves_approx/fullCtx
        │
        ▼
State.recover_psi_commute_approx_of_indep   (local Theorem 61)
        │
        ▼
self-step recovery lemmas ──► SameFiber / SamePresence / SameProvision
        │
        ▼
PsiFiberAgrees_of_sameFiberAt ──► recovery_exactness_aux
PsiConfinedAgrees_of_confined ──► recovery_exactness_recoverAcc
                                      │
                                      ▼
                              recovery_exactness_cor62*
```

Specific dependencies:

- `State.recover_psi_commute_approx_of_indep` depends on
  `State.recover_writeEffect_approx`, `Iterator.Independent.comm`, and
  `Iterator.InTransformMonoid`;
- `Step.psi_preserves_approx` depends on `Step.psi_preserves_sameFiberAt` and
  `State.writeEffect_preserves_approx`;
- `Step.psi_preserves_fullCtx` depends on `Step.psi_preserves_approx`,
  `State.fullCtx_of_nodup_of_disjoint`, and `PsiConfinedAt`;
- trace induction uses `Step.psi_preserves_nodupKeys` /
  `Step.psi_preserves_pairwiseDisjointTables` and
  `Step.psiConfinedAt_self_of_pair_left/right` to advance the local
  well-formedness hypotheses;
- the non-`n` step case of `recovery_exactness_aux` uses
  `State.Approx.trans hedit' hcomm' hpsi`, while the `n` step case uses
  `hself'`.

## 6. Correspondence to the Paper

| Paper | Formalization |
| --- | --- |
| Def 43 Component | `Component`, with iterator running on `Ctx K V = FullCtx` |
| Def 44 Fiber | `Fiber` |
| Def 45 Registry | `Registry`, `lookup`, `set` |
| Def 46 target view / quiescence | `targetOf`, `quiet` |
| Def 48 writes half | `ConfinedIterator`, `ConfinedAcc`, `Component.Confined`, `Lifecycle.Confined` |
| Def 49 four-state lifecycle | `Lifecycle` (inactive / loading / active / unloading) |
| Def 50 withdrawal guard | `relied` |
| Def 51/52 effect iterator | `Iterator`, `Iterator.Witnessed`, `Iterator.WitnessedAll`, `Iterator.Lifts` |
| Eq. 40 active sigma | `sigmaOf` (active-only) |
| Full context `Γ∞` | `Full.FullCtx K V = (ambient, rawSigma)`; `State.fullCtx` uses `rawSigma` |
| Eq. 52 | `Step.factorization : next st = edit st (psi st s)` |
| Definition 60 / Eq. 54–55 | `Iterator.InTransformMonoid`, `Iterator.Independent`, `Iterator.PairwiseIndependent` |
| Theorem 61 | Local: `State.recover_psi_commute_approx_of_indep`; trace-level: `StepTrace.recovery_exactness_recoverAcc` |
| Corollary 62 | `StepTrace.recovery_exactness_cor62` and `_wellformed` / `_fiber_stable` / `_confined` |
| Eq. (56) / withdrawal | `State.Withdraws`, `State.WithdrawsOn`, `Step.SelfWithdrawsAt` |

## 7. Current Side Conditions and Future Work

The trace-level Corollary 62 currently takes explicit side conditions:

- `Iterator.Independent` / `Iterator.InTransformMonoid`;
- `NodupKeys` / `PairwiseDisjointTables` (already eliminated by
  `_wellformed`);
- `Step.Confined` / write-confined iterators and accumulators;
- `Step.SelfWithdrawsAt` / `State.Withdraws` / `State.WithdrawsOn`;
- trace-local `PsiFiberAgrees` / `PsiConfinedAgrees` (already derivable from
  `SameFiberAt` and write-confinement).

Recovered metatheory (ported from the deleted legacy modules):

- Definition 58 / Theorem 59: `LeanCordix/WellFormed.lean`;
- Theorem 66 progress/termination: `LeanCordix/Progress.lean` and
  `LeanCordix/Termination.lean`;
- Lemma 54/57: `LeanCordix/Vestigial.lean`;
- Lemma 55/56: `LeanCordix/Invariance.lean` and
  `LeanCordix/Equivariance.lean`;
- Theorem 64: `LeanCordix/Coherence.lean`;
- Table-confinement machinery: `LeanCordix/TableConfined.lean`.

Possible next steps:

1. Derive `hconf_iter` / `hconf_acc` from the ported
   `Component.TableConfined` / `Registry.TableConfined` preservation
   theorems;
2. Finish the remaining combinatorial half of Theorem 66.2 (the
   per-interval bound `B = len n + 4`) and then the full confluence proof
   (Theorem 73) using the recovered Lemma 55/56/57 and termination pieces.
