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
| `LeanCordix.Iterator` | §4.3.2, 4.3.4 | Effect iterators with errors (Defs 51/52, Eq. 49), their witnessed step relation, the `Lifts` relation for complete successful runs, and the embedding of plain effects. |
| `LeanCordix.FullCalculus` | §4.3–4.4 | The full ten-rule calculus: four-state lifecycle (Def 49), `L-Begin`, `L-Iter`, `L-Finish`, `L-Divert` (abort and landing), `L-Raise`, `L-Leave`, `L-Unload`, plus `O-Insert`/`O-Retire`/`O-Remove`. Defines full `WellFormed` (Def 58, all four clauses), proves **preservation of all four clauses under all ten rules** (Thm 59), and proves the explicit disjunction form of **progress** (Thm 66.1): a non-quiescent state either has a lifecycle step or a guarded unloading fiber. |

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
  (Thm 59); the explicit disjunction form of full progress (Thm 66.1).

Left as future work: the confinement discipline (Def 48) and the global
metatheory that builds on it together with acyclicity of precedence
(§4.4.2–4.4.5: recovery exactness, resolution coherence, termination,
confluence).  The guarded-unload disjunct of the full progress theorem is
not yet discharged by the acyclicity argument of Theorem 66; it requires
the confinement invariant (dom σ_n ⊆ P_n) from Definition 48.

## Building

```
lake build
```
