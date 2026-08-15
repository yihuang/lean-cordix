# lean-cordix

A formalization in Lean 4 of the formal core of

> *A Programming Paradigm for Spatiotemporal Composability* — Yifan Shi,
> Wei Zhang, Tianyi Cui (Peking University, DeepSeek-AI).

The paper (cordix.pdf) develops **Cordix / Cordis**: a programming paradigm
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

Left as future work (documented in `LeanCordix.Calculus`): the ten-rule
calculus of §4.3 (effect iterators, the guarded withdrawal of Def 50,
asynchrony, failure), the confinement discipline (Def 48), and the global
metatheory built on those (§4.4.2–4.4.5: recovery exactness, resolution
coherence, termination, confluence).  The paper notes that well-formedness
clauses (3)–(4) and Theorem 63 (2)–(3) belong to the guarded calculus.

## Building

```
lake build
```
