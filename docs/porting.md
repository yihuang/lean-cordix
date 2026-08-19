# Porting deleted legacy metatheory into the faithful full-context model

Goal: recover the valuable theorems deleted by commit `79c0f00`
("Refactor full-context model into flat modules and remove legacy") by
porting them onto the current faithful model, not by restoring the old
`Cordix.Full` code verbatim.

## Repository facts

- Current library root: `LeanCordix.lean` (do NOT modify during subagent work).
- Current canonical modules:
  - `LeanCordix/Basic.lean` — `Component`, `Lifecycle`, `Fiber`,
    `Registry`, `State`, `lookup/set/del`, `NodupKeys`,
    `PairwiseDisjointTables`, `sigmaOf`, `rawSigma`, `targetOf`, `quiet`,
    `relied`, `recover`, `writeEffect`, `SameFiberAt`.
  - `LeanCordix/Step.lean` — `Step`, `Step.name`, `Step.kind`,
    `Step.psi`, `Step.edit`, `Step.next`, `Step.factorization`,
    `Step.Confined`, `Step.PsiConfinedAt`.
  - `LeanCordix/Approx.lean` — `State.Approx`, rawSigma splitting,
    local Theorem 61.
  - `LeanCordix/Recovery.lean` — self-step recovery, `SameFiber`,
    confinement transfer.
  - `LeanCordix/Trace.lean` — `StepTrace`, `foldPsiExcept`,
    trace-level Theorem 61 / Corollary 62.
- Namespace: current model lives directly in `namespace Cordix`
  (not `Cordix.Faithful`, not `Cordix.Full`).
- Old legacy files are available at `/tmp/oldrepo/*.lean` and in git as
  `HEAD~1:LeanCordix/<File>.lean`.

## Current key type signatures

```lean
namespace Cordix

abbrev Ctx (K : Type) (V : K → Type u) : Type _ := Full.FullCtx K V
-- FullCtx K V = CoefCtx K V × CoefCtx K V

structure Component (K : Type) (V : K → Type u) (E : Type) where
  spec : Spec K
  prov : List K
  iter : Iterator (Ctx K V) E
  wit : Iterator.WitnessedAll iter

inductive Lifecycle (N : Type) (K : Type) (V : K → Type u) (E : Type)
  | inactive (outcome : Option E)
  | loading (iter : Iterator (Ctx K V) E) (acc : Ctx K V → Ctx K V) (view : K → Option N)
  | active (acc : Ctx K V → Ctx K V) (view : K → Option N)
  | unloading (acc : Ctx K V → Ctx K V) (view : K → Option N) (outcome : Option E)

structure Fiber (N : Type) (K : Type) (V : K → Type u) (E : Type) where
  comp : Component K V E
  parent : Option N
  table : CoefCtx K V
  retired : Bool
  lc : Lifecycle N K V E

abbrev Registry (N K : Type) (V : K → Type u) (E : Type) := List (N × Fiber N K V E)

structure State (N : Type) (K : Type) (E : Type) (V : K → Type u) where
  reg : Registry N K V E
  ambient : CoefCtx K V

inductive Step (s : State N K E V) : Type (max 1 u) where
  | oInsert (n : N) (c : Component K V E) (p : Option N) ... : Step s
  | oRetire ... | oRemove ... | lBegin ... | lIter ... | lFinish ...
  | lRaise ... | lDivertAbort ... | lDivertLand ... | lLeave ...
  | lUnload ...

inductive StepTrace : State N K E V → State N K E V → Type (max 1 u)
  | nil (s) : StepTrace s s
  | cons {s₁ s₂ s₃} (st : Step s₁) (hnext : Step.next st = s₂)
      (ht : StepTrace s₂ s₃) : StepTrace s₁ s₃
```

Important:
- `Step.kind` returns `Full.StepKind` from `LeanCordix/StepKind.lean`.
  The constructors are `oInsert`, `oRetire`, `oRemove`, `lBegin`,
  `lIter`, `lFinish`, `lRaise`, `lDivertAbort`, `lDivertLand`,
  `lLeave`, `lUnload`.
- `State.sigmaOf` is active-only sigma (paper Eq. 40).
- `State.fullCtx` uses `rawSigma` (all tables, regardless lifecycle).
- Registry operations `lookup`, `set`, `del` are already in `Basic.lean`.

## Work rules for subagents

1. Create only your assigned new file(s). Do not edit existing Lean files,
   do not edit `LeanCordix.lean`, do not edit `docs/design.md`.
2. Use `import LeanCordix.Basic` / `import LeanCordix.Step` / etc. as
   needed. You may import other current modules.
3. Test each new file with:
   ```bash
   lake env lean LeanCordix/<YourFile>.lean
   ```
   It must exit 0. You may iterate locally.
4. Old code is a *reference*; adapt namespaces/types. Do not blindly copy
   `Cordix.Full` code. Use current `State`, `Step`, `StepTrace`,
   `Full.StepKind`, etc.
5. Do not introduce `sorry`, `admit`, `axiom`, or `unsafe`.
6. If a theorem is impossible to port exactly, either:
   - port the closest current-model statement, or
   - leave a clearly documented `theorem ... := by` with no sorry? No:
     do not leave unfinished theorems. If blocked, report in your final
     message and stop without a broken file.
7. Keep files reasonably focused and add doc comments mapping to paper
   definitions/theorems.

## Assignments

### Agent A — `LeanCordix/WellFormed.lean`

Port Definition 58 (WellFormed) and Theorem 59 (Preservation) to the
current faithful model.

Reference old files:
- `/tmp/oldrepo/FullCalculus.lean` (`WellFormedBase`, `WellFormed`,
  `wellFormedBase_*`, `wellFormed_*`, `WellFormed.preserved`)
- `/tmp/oldrepo/Calculus.lean` (base-calculus variant, useful for
  clauses 1–2)

Suggested contents:
- `WellFormedBase` / `WellFormed` structures adapted to current
  `Registry`/`State`.
- Lemmas for `set` / `del` / lifecycle updates preserving well-formedness.
- `WellFormed.preserved` for every current `Step.next`.

### Agent B — `LeanCordix/Progress.lean` and `LeanCordix/Termination.lean`

Port Theorem 66 (Progress / Termination) scaffolding.

Reference old files:
- `/tmp/oldrepo/FullCalculus.lean` (`exists_lstep_of_not_quiet`,
  `no_lstep_of_quiet`, `Precedes`, `Acyclic`)
- `/tmp/oldrepo/Termination.lean` (`Step.StepTrace.length`,
  `countFor`, `targetTurns`, `countFor_le_length`,
  `countFor_le_mul_of_interval_bound`)

Suggested contents:
- `Precedes`, `Acyclic` adapted to current registry/state.
- `exists_lstep_of_not_quiet` (no-deadlock) for current `Step`.
- `no_lstep_of_quiet`.
- Termination quantities on current `StepTrace`:
  `length`, `countFor`, `targetTurns`.
- The combinatorial bound lemmas from old `Termination.lean`.

### Agent C — `LeanCordix/Vestigial.lean`

Port Lemma 54/57 (vestigial entries) and step-local preservation lemmas.

Reference old files:
- `/tmp/oldrepo/TraceModel.lean` (`Vestigial`, `sigmaOf_del_eq_of_vestigial`,
  `providerOf_del_eq_of_vestigial`, `targetOf_del_eq_of_vestigial`,
  `relied_del_eq_of_vestigial`, `step_del_of_vestigial`,
  `step_of_del_vestigial`, `lookup_next_eq_of_ne`,
  `table_next_eq_of_not_writesTable`, `retired_monotone`, etc.)
- Current equivalents already in `Basic.lean`/`Step.lean`; only add what is
  missing.

Suggested contents:
- `Vestigial s n` adapted to current `State`.
- `sigmaOf_del_eq_of_vestigial` etc.
- `step_del_of_vestigial` / `step_of_del_vestigial` for current `Step`.
- Local step lemmas not already in `Step.lean`.

### Agent D — `LeanCordix/Invariance.lean` and `LeanCordix/Equivariance.lean`

Port Lemma 55 (observational state equivalence / step transport) and
Lemma 56 (name renaming / equivariance).

Reference old files:
- `/tmp/oldrepo/Invariance.lean` (`Lifecycle.Equiv`, `Fiber.Equiv`,
  `State.Equiv`, `step_transport`, `step_equiv`)
- `/tmp/oldrepo/Equivariance.lean` (`NameEquiv`, `Rename.*`,
  `step_rename`, `step_rename_bwd`)

Suggested contents:
- `State.Equiv` / `Lifecycle.Equiv` / `Fiber.Equiv` adapted to current
  `FullCtx`-based types.
- `step_transport` and `step_equiv` for current `Step`.
- `NameEquiv`, `Rename.registry`, `Rename.state`, `lookup_rename`,
  `sigmaOf_rename`, `providerOf_rename`, `targetOf_rename`,
  `relied_rename_iff`, `step_rename`.

### Agent E — `LeanCordix/Coherence.lean`

Port Theorem 64 (Resolution coherence).

Reference old file:
- `/tmp/oldrepo/Global.lean`
  (`Step.StepTrace.ViewFixedAlong`,
   `Step.kind_of_loading_lifecycle`,
   `Step.kind_of_unloading_lifecycle`,
   `Step.next_unloading_of_loading_exit`,
   `Step.view_preserved_of_iter`,
   `Step.target_eq_of_iter_view`,
   `StepTrace.view_fixed_of_iteration_trace`,
   `StepTrace.resolution_coherent_of_iteration_trace`)

Suggested contents:
- `ViewFixedAlong` adapted to current `StepTrace`.
- Lemmas about lifecycle kind, view preservation along iteration steps.
- `resolution_coherent_of_iteration_trace` (Theorem 64 faithful form).

## Integration

After all agents finish, the main agent will:
- add imports to `LeanCordix.lean`;
- run `lake build`;
- fix cross-module issues;
- update `README.md` / `docs/design.md` to mention the recovered
  metatheory.
