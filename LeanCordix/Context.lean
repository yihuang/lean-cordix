import LeanCordix.Revertible
import LeanCordix.Coeffect

/-!
# Cordix — Section 3.3: The Context Paradigm

This module formalizes Section 3.3 of *A Programming Paradigm for
Spatiotemporal Composability* (Cordix/Cordis): the unification of the effect
context and the coeffect context into a single context type.

Formalized content:
* Definition 32 — the unified context `Γ∞ = Γ × (Γ → Γ) × Σ` (one level of
  the recursive tower; iterating the construction yields the tower).
* Definition 33 — observational equivalence of contexts, assembled from
  per-key equivalences on the coeffect values.
* Related contexts agree on satisfaction and on `notify` (reactivity is a
  property of `Σ/≃`).
* Theorem 40 (core case) — operations at distinct keys are independent: the
  `set` operations of Definition 23 at distinct keys commute, and neither
  disturbs the inverse the other yields.
-/

namespace Cordix

universe u

variable {K : Type} [DecidableEq K] {V : K → Type u}

/-! ## Definition 32: the unified context -/

/-- **Definition 32.** The unified context at one level of the tower:
a context state together with its accumulator (Definition 2) and the
coeffect context carrying dependency information (Definition 22).  The
recursive construction `Γ∞ = E_Γ.Γ × (Γ → Γ) × Σ` of the paper is obtained
by iterating; `effect` maps `E_Γ` to itself, unifying the tower into a
single self-similar type. -/
structure UnifiedCtx (Γ : Type u) (K : Type) (V : K → Type u) where
  /-- The previous-level context state. -/
  state : Γ
  /-- The accumulator, which recovers this level's effects. -/
  acc : Γ → Γ
  /-- The coeffect context carrying dependency information. -/
  coeffect : CoefCtx K V

/-- The coeffect projection of a unified context. -/
abbrev UnifiedCtx.σ {Γ : Type u} {K : Type} {V : K → Type u}
    (γ : UnifiedCtx Γ K V) : CoefCtx K V := γ.coeffect

/-- The effect context projection of a unified context. -/
abbrev UnifiedCtx.effectCtx {Γ : Type u} {K : Type} {V : K → Type u}
    (γ : UnifiedCtx Γ K V) : EffectCtx Γ := (γ.state, γ.acc)

/-- The initial unified context over `γ₀` with no dependencies. -/
def UnifiedCtx.init (γ₀ : Γ) : UnifiedCtx Γ K V where
  state := γ₀
  acc := id
  coeffect := fun _ => none

/-! ## Definition 33: observational equivalence -/

variable (R : (k : K) → V k → V k → Prop)

/-- **Definition 33.** Two coeffect contexts are related when they bind the
same keys to related values. -/
def CoefCtx.obsEquiv (σ σ' : CoefCtx K V) : Prop :=
  (∀ k, CoefCtx.definedAt σ k ↔ CoefCtx.definedAt σ' k)
    ∧ ∀ k, ∀ w : V k, ∀ w' : V k, σ k = some w → σ' k = some w' → R k w w'

/-- **Definition 33.** Two states of a unified context are related when
their coeffect projections are. -/
def UnifiedCtx.obsEquiv (γ γ' : UnifiedCtx Γ K V) : Prop :=
  CoefCtx.obsEquiv R γ.σ γ'.σ

variable {R}

omit [DecidableEq K] in
/-- Reflexivity of observational equivalence. -/
theorem CoefCtx.obsEquiv_refl (σ : CoefCtx K V)
    (hR : ∀ k (v : V k), R k v v) : CoefCtx.obsEquiv R σ σ :=
  ⟨fun k => Iff.rfl, fun k w w' hw hw' => by
    have e : some w = some w' := hw.symm.trans hw'
    have e2 : w = w' := Option.some.inj e
    subst e2
    exact hR k _⟩

omit [DecidableEq K] in
/-- **Reactivity is a property of `Σ/≃`.** Related states agree on the
satisfaction predicate, and hence on the classification `notify`. -/
theorem satisfies_obsEquiv (S : Spec K) (σ σ' : CoefCtx K V)
    (h : CoefCtx.obsEquiv (fun _ _ _ => True) σ σ') :
    satisfies σ S ↔ satisfies σ' S := by
  constructor <;> intro hs k hk
  · exact (h.1 k).mp (hs k hk)
  · exact (h.1 k).mpr (hs k hk)

omit [DecidableEq K] in
theorem notify_obsEquiv (S : Spec K) (σ σ' τ τ' : CoefCtx K V)
    (h : CoefCtx.obsEquiv (fun _ _ _ => True) σ σ')
    (h' : CoefCtx.obsEquiv (fun _ _ _ => True) τ τ') :
    notify S σ τ = notify S σ' τ' := by
  have e1 : satisfies σ S ↔ satisfies σ' S := satisfies_obsEquiv S σ σ' h
  have e2 : satisfies τ S ↔ satisfies τ' S := satisfies_obsEquiv S τ τ' h'
  by_cases a : satisfies σ S <;> by_cases c : satisfies τ S
  · have b : satisfies σ' S := e1.mp a
    have d : satisfies τ' S := e2.mp c
    simp [notify, a, b, c, d]
  · have b : satisfies σ' S := e1.mp a
    have d : ¬satisfies τ' S := fun hh => c (e2.mpr hh)
    simp [notify, a, b, c, d]
  · have b : ¬satisfies σ' S := fun hh => a (e1.mpr hh)
    have d : satisfies τ' S := e2.mp c
    simp [notify, a, b, c, d]
  · have b : ¬satisfies σ' S := fun hh => a (e1.mpr hh)
    have d : ¬satisfies τ' S := fun hh => c (e2.mpr hh)
    simp [notify, a, b, c, d]

/-! ## Theorem 40 (core case): operations at distinct keys are independent -/

variable (k k' : K)

/-- **Theorem 40 (forward commutation).** The `set` operations of
Definition 23 at distinct keys commute as transformations of the coeffect
context. -/
theorem CoefCtx.bind_bind_comm (hk : k ≠ k') (v : V k) (v' : V k')
    (σ : CoefCtx K V) :
    bind (bind σ k v) k' v' = bind (bind σ k' v') k v := by
  funext k''
  by_cases h : k'' = k
  · subst h
    simp [bind, hk]
  · by_cases h' : k'' = k'
    · subst h'
      simp [bind, Ne.symm hk]
    · simp [bind, h, h']

/-- **Theorem 40 (inverses undisturbed).** The restriction that inverts a
`set` at one key neither disturbs nor is disturbed by a `set` at a distinct
key. -/
theorem CoefCtx.restrict_bind_comm (hk : k ≠ k') (v : V k)
    (σ : CoefCtx K V) :
    restrict (bind σ k v) k' = bind (restrict σ k') k v := by
  funext k''
  by_cases h : k'' = k
  · subst h
    simp [restrict, bind, hk]
  · by_cases h' : k'' = k'
    · subst h'
      simp [restrict, bind, Ne.symm hk]
    · simp [restrict, bind, h, h']

end Cordix
