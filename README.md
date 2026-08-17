# lean-cordix

A formalization in Lean 4 of the formal core of

> *A Programming Paradigm for Spatiotemporal Composability* — Yifan Shi,
> Wei Zhang, Tianyi Cui (Peking University, DeepSeek-AI).

[The paper](https://github.com/cordiverse/paper) develops **Cordix / Cordis**: a programming paradigm
where a *single unified context* carries both *revertible effects* (every
context transformation carries an inverse the runtime tracks) and *reactive
coeffects* (each change of the context is classified against a component's
coeffect specification), and a *calculus of dynamic composition* whose
metatheory carries spatiotemporal composability from a single component to a
whole system.

## Contents

| Module | Paper | Content |
| --- | --- | --- |
| `LeanCordix.Revertible` | §3.1 | Twisted composition monoid, effect context, `track`/`recover` (Thms 4–7), effect functions & `⋄` (Thms 10–11), the lift `effect` (Thms 13–15), LIFO reversion (Thm 16), transformation monoids & independence (Defs 17–19, Lemma 18). |
| `LeanCordix.Coeffect` | §3.2 | The coeffect context `Σ = (k : K) ⇀ V_k`, `get`/`set`/restriction (Defs 22–23; `set` is a witnessed effect function), specifications, satisfaction, and `notify` (Defs 25–26), coeffects at a key (Def 24), isolation and interception (Defs 28–31). |
| `LeanCordix.Context` | §3.3 | The unified context (Def 32), observational equivalence (Def 33), agreement on satisfaction/`notify` (reactivity is a property of `Σ/≃`), and distinct-key independence of `set` operations (Thm 40, core case). |
| `LeanCordix.Calculus` | §4.1–4.2, 4.4 | Components, fibers, the registry and `Σ_γ` (Defs 43–45), target views & quiescence (Def 46), the withdrawal guard (Def 50), the five base-calculus rules, well-formedness (Def 58), **preservation** of clauses (1)–(2) (Thm 59), **ordering** first claim (Thm 63, Eq. 58), and **progress / no deadlock** for the base calculus (Thm 66.1). |
| `LeanCordix.Iterator` | §4.3.2, 4.3.4 | Effect iterators with errors (Defs 51/52, Eq. 49), their witnessed step relation, `Reachable` continuations and the full-iterator witness `WitnessedAll`, the `Lifts` relation for complete successful runs with **soundness of complete runs** (`soundness_lifts`), and the embedding of plain effects. |
| `LeanCordix.Equivariance` | §4.4 | Lemma 56 support: injective renaming of names across views, lifecycle states, fibers, registries, and states, with commutation of `lookup`, `sigmaOf`, `providerOf`, `targetOf`, `relied`, and full equivariance of every `Step` record, including the next-state equation (`step_rename`, `step_rename_next`, `step_rename_bwd`). |
| `LeanCordix.TraceModel` | §4.4 | The trace-indexed model `edit ∘ Ψ`: a `State` structure carrying the registry plus the ambient context, a **Type-level step record** `Step` with explicit `name` and `kind` fields, the state map `Ψ` and the edit `edit` as ordinary functions `State → State`, the factorization `next st = edit st (Ψ st)` (Eq. 52), Lemma 54, Type-level `StepTrace` preservation, and Lemma 57 (vestigial entries: deletion lemmas, step transport, and step lifting with the explicit insertion/removal conflicts). |
| `LeanCordix.Invariance` | §4.4 | Lemma 55: observational `Lifecycle.Equiv` and `State.Equiv` with symmetry, pointwise fiber fields, derived congruence of `targetOf`/`relied`, preservation of the domain and fields by `set`/`del`, preservation of `sigmaOf`/`providerOf` by contribution-preserving updates, fresh insertions, unloading the unique table provider, and finishing a table-confined activation; **step transport** of every `Step` constructor across `State.Equiv` (`step_transport`, same name and kind) and **next-state preservation** (`step_equiv`) under `WellFormed`, `TableProv`, and `Registry.TableConfined`. |
| `LeanCordix.FullCalculus` | §4.3–4.4 | The full ten-rule calculus: four-state lifecycle (Def 49), `L-Begin`, `L-Iter`, `L-Finish`, `L-Divert` (abort and landing), `L-Raise`, `L-Leave`, `L-Unload`, plus `O-Insert`/`O-Retire`/`O-Remove`. Defines full `WellFormed` (Def 58, all four clauses), proves **preservation of all four clauses under all ten rules** (Thm 59) and **along finite traces**, packages the confinement-derived invariants as `ConfinedWellFormed` and proves **their preservation under all ten rules** (Thm 59 again), adds the **table-aware lifecycle relation** `LstepT`/`TStep`, **proves preservation under table-aware steps** (`ConfinedWellFormed.preservedT`), packages `TableConfinedWellFormed` with component confinement and loading-iterator reachability, **proves table-aware lifecycle trace preservation**, and **proves table-aware progress** (`exists_lstepT_of_not_quiet`).  It also proves **progress** (Thm 66.1) under acyclicity plus those invariants (`exists_lstep_of_not_quiet`), and **quiescence is sound** (`no_lstep_of_quiet`). |
| `LeanCordix.Global` | §4.4.2–4.4.3 | The start of the global metatheory: the effect-side relation `State.Approx` (paper `≈`) comparing ambient and raw tables while forgetting control fields; `State.writeTable` and **`Ψ` preserves `≈`** (`State.writeTable_preserves_approx`, `Step.psi_preserves_approx`); `ControlOnly` steps and the **control-only recovery-exactness step/trace lemmas** (`Step.edit_control_preserves_approx`, `StepTrace.recovery_exactness_control_trace`); **Equation (52) up to `≈` for every non-`O-Remove` rule** (`Step.edit_approx_psi_of_ne_remove`); **trace-level Equation (52)** (`Step.StepTrace.foldPsi`, `StepTrace.foldPsi_preserves_approx`, `StepTrace.next_approx_foldPsi`) and **recovery exactness for an episode with no `n` steps** (`StepTrace.recovery_exactness_no_steps_of`); type-level trace predicates; and the **resolution-coherence core of Theorem 64** (`Step.view_preserved_of_iter`, `Step.target_eq_of_iter_view`, `StepTrace.view_fixed_of_iteration_trace`, `StepTrace.resolution_coherent_of_iteration_trace`), plus the **loading-step dichotomy** `Step.kind_of_loading_lifecycle`, the **leaving-loading half** `Step.next_unloading_of_loading_exit`, and the **unloading-closing half** `Step.kind_of_unloading_lifecycle`. |
| `LeanCordix.Termination` | §4.4.4 | Termination scaffolding for Thm 66.2: `Step.StepTrace.length`, `countFor`, and `targetTurns` (Eq. 61), with `countFor_eq_zero_of_no_steps`, `countFor_le_length`, and `targetTurns_le_length`; **interval splitting** (`append`, `SourceTargetConst`, `Split`, `splitFirstInterval`), and the **combinatorial half of Theorem 66.2** (`countFor_le_mul_of_interval_bound`, `countFor_le_targetTurns_of_len`): if every source-constant interval has at most `B` steps on a fiber, then `countFor ht n ≤ B * (targetTurns ht n + 1)`; plus the loading/non-loading lifecycle decomposition (`IsLoadingKind`, `IsNonLoadingKind`, `loadingCount`, `nonLoadingCount`, `countFor_eq_loading_add_nonLoading`). |

## Scope

All of the formalized definitions and the following results carry full proofs:

* §3.1 — Theorems 4, 5, 7, 10, 11, 13, 14, 15, 16, and Lemma 18.
* §3.2 — `set` is witnessed (restriction undoes binding on its domain),
  decidable satisfaction, the trichotomy of `notify`.
* §3.3 — related states agree on satisfaction and `notify`; `set` operations
  at distinct keys commute and do not disturb each other's inverses.
* §4.2/4.4 — preservation (Thm 59) of clauses (1)–(2) under all five rules,
  the first ordering claim (Thm 63, Eq. 58), and no-deadlock progress
  (Thm 66, clause 1) for the base calculus.
* §4.3/4.4 — full ten-rule calculus with iterators and failure; full
  preservation of all four well-formedness clauses under all ten rules
  (Thm 59); preservation of `ConfinedWellFormed` under all ten rules and
  under the table-aware calculus `LstepT`/`TStep`; full progress (Thm 66.1)
  under acyclicity of precedence plus the confinement-derived invariants;
  quiescence soundness.
* §4.4.2/4.4.3 — the effect-side relation `≈` (`State.Approx`); every
  `Ψ` preserves `≈` (`Step.psi_preserves_approx`); the control-only
  recovery-exactness step and trace lemmas; Equation (52) up to `≈` for
  every non-`O-Remove` rule (`Step.edit_approx_psi_of_ne_remove`);
  trace-level Equation (52) via `foldPsi`; recovery exactness for an
  episode with no steps of the tracked fiber; and the resolution coherence
  core of Theorem 64: in an iteration-only initial interval the committed
  view is fixed and every `L-Iter`/`L-Finish` runs against the same
  resolution `v`; and a lifecycle step from `loading` is one of
  `L-Iter`/`L-Finish`/`L-Raise`/`L-Divert` (`Step.kind_of_loading_lifecycle`);
  leaving `loading` via `L-Raise`/`L-Divert` lands in `unloading`
  (`Step.next_unloading_of_loading_exit`); and once a fiber is `unloading`,
  the only lifecycle step on it is `L-Unload`
  (`Step.kind_of_unloading_lifecycle`).
* §4.4.4 — termination scaffolding: `length`, `countFor`, `targetTurns`,
  `countFor_le_length`, `targetTurns_le_length`, the interval-splitting
  machinery `append`/`SourceTargetConst`/`Split`/`splitFirstInterval`, and
  the combinatorial half of Thm 66.2:
  `countFor_le_mul_of_interval_bound` and the packaged
  `countFor_le_targetTurns_of_len`; and the loading/non-loading lifecycle
  decomposition `loadingCount`/`nonLoadingCount` with
  `countFor_eq_loading_add_nonLoading`.

Left as future work: the full recovery-exactness theorem with pairwise
independence of iterators (Theorem 61 and Corollary 62 in full generality),
the per-interval `len n + 4` bound that instantiates the combinatorial
termination bound (the remaining part of Thm 66.2), confluence (Thm 73),
and the remaining global composability theorems beyond the material now
proved in `TraceModel` and `Global`.

## Building

```
lake build
```
