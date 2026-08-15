import LeanCordix.Revertible
/-!
# Cordix — Section 3.2: Reactive Coeffects

This module formalizes Section 3.2 of *A Programming Paradigm for Spatiotemporal
Composability* (Cordix/Cordis): reactive coeffects, in which each change of the
context is classified against a component's coeffect specification, driving
activation and deactivation.

Formalized content:
* Definition 22 — the coeffect context `Σ = (k : K) ⇀ V_k`, a dependent
  partial function.  (The paper's finite partial functions are modelled as
  plain dependent partial functions; finiteness is used in the paper only to
  decide satisfaction, which here follows from the finiteness of the
  specification.)
* Definition 23 — `get` and `set`; `set` is a witnessed effect function on `Σ`
  whose inverse is restriction.
* Definition 24 — coeffects as triples `(V_k, ≃, O_k)`.
* Definition 25 — coeffect specifications.
* Definition 26 — satisfaction `σ ⊨ S` and the classification `notify_S`.
* Definitions 28–29 — coeffect isolation (realms).
* Definitions 30–31 — coeffect interception (metadata).
-/



namespace Cordix

universe u v

variable {K : Type} [DecidableEq K] {V : K → Type u}

/-! ## Definition 22: the coeffect context -/

/-- **Definition 22.** The coeffect context `Σ = (k : K) ⇀ V_k`: a dependent
partial function assigning to each defined key `k` a value of type `V k`. -/
abbrev CoefCtx (K : Type) (V : K → Type u) : Type _ := (k : K) → Option (V k)

namespace CoefCtx

variable {σ σ' : CoefCtx K V}

/-- `k ∈ dom σ`: the key is defined. -/
def definedAt (σ : CoefCtx K V) (k : K) : Prop := (σ k).isSome

omit [DecidableEq K] in
theorem definedAt_iff (σ : CoefCtx K V) (k : K) :
    definedAt σ k ↔ ∃ w, σ k = some w :=
  Option.isSome_iff_exists

/-- **Definition 23.** `get`: application, defined when `k ∈ dom σ`. -/
def get (σ : CoefCtx K V) (k : K) (h : definedAt σ k) : V k :=
  (σ k).get h

/-- Binding: `σ[k ↦ v]` binds `k` to `v`, agreeing with `σ` elsewhere. -/
def bind (σ : CoefCtx K V) (k : K) (v : V k) : CoefCtx K V :=
  fun k' => if h : k' = k then some (h ▸ v) else σ k'

/-- Restriction: `σ ∖ k` removes `k` from the domain, agreeing elsewhere. -/
def restrict (σ : CoefCtx K V) (k : K) : CoefCtx K V :=
  fun k' => if k' = k then none else σ k'

theorem bind_self (σ : CoefCtx K V) (k : K) (v : V k) : bind σ k v k = some v := by
  simp [bind]

theorem bind_other (σ : CoefCtx K V) (k k' : K) (v : V k) (hne : k' ≠ k) :
    bind σ k v k' = σ k' := by
  simp [bind, hne]

theorem restrict_self (σ : CoefCtx K V) (k : K) : restrict σ k k = none := by
  simp [restrict]

theorem restrict_other (σ : CoefCtx K V) (k k' : K) (hne : k' ≠ k) :
    restrict σ k k' = σ k' := by
  simp [restrict, hne]

/-- **Definition 23 (set as an effect function).** `set (k, v)` is the effect
function on `Σ` mapping `σ` to `(σ[k ↦ v], σ' ↦ σ' ∖ k)`: its first component
is the binding and its second the restriction it yields as inverse. -/
def set (k : K) (v : V k) : Eff (CoefCtx K V) :=
  fun σ => (bind σ k v, fun σ' => restrict σ' k)

/-- **Definition 23 (witness).** `set (k, v)` is witnessed on its domain:
restriction undoes binding at every state satisfying the precondition
`k ∉ dom σ` (a dependency cannot be provided twice). -/
def SetWitnessed (k : K) (v : V k) : Prop :=
  ∀ σ : CoefCtx K V, σ k = none → (set k v σ).2 ((set k v σ).1) = σ

theorem set_witnessed (k : K) (v : V k) : SetWitnessed k v := by
  intro σ hnone
  show (restrict (bind σ k v) k) = σ
  funext k'
  by_cases h : k' = k
  · subst h
    simp [restrict, hnone]
  · simp [restrict, bind, h]

end CoefCtx

/-! ## Definitions 25–26: specifications, satisfaction, notification -/

/-- **Definition 25.** A coeffect specification: the (finite) set of
dependencies a component declares from the environment. -/
abbrev Spec (K : Type) := List K

/-- Satisfaction: `σ ⊨ S` when every declared key is defined in `σ`. -/
def satisfies (σ : CoefCtx K V) (S : Spec K) : Prop :=
  ∀ k ∈ S, CoefCtx.definedAt σ k

/-- Satisfaction is decidable (the paper's finiteness; classically here). -/
noncomputable instance decidableSatisfies (σ : CoefCtx K V) (S : Spec K) :
    Decidable (satisfies σ S) := Classical.propDecidable _

/-- **Definition 26.** The classification of a transition `σ → σ'` against a
specification `S`: activating, deactivating, or neutral. -/
inductive Notify
  | activating
  | deactivating
  | neutral
deriving DecidableEq

/-- **Definition 26.** `notify_S (σ, σ')` classifies a state transition
against the specification `S`. -/
noncomputable def notify (S : Spec K) (σ σ' : CoefCtx K V) : Notify :=
  if satisfies σ S ∧ ¬satisfies σ' S then Notify.deactivating
  else if ¬satisfies σ S ∧ satisfies σ' S then Notify.activating
  else Notify.neutral

omit [DecidableEq K] in
/-- `notify` is neutral exactly when the satisfaction status is unchanged. -/
theorem notify_neutral_iff (S : Spec K) (σ σ' : CoefCtx K V) :
    notify S σ σ' = Notify.neutral ↔ (satisfies σ S ↔ satisfies σ' S) := by
  by_cases h₁ : satisfies σ S <;> by_cases h₂ : satisfies σ' S <;>
    simp [notify, h₁, h₂]

omit [DecidableEq K] in
/-- Related contexts agree on satisfaction.  (Section 3.3.2: reactivity is a
property of `Σ/≃`.) -/
theorem satisfies_congr (S : Spec K) (σ σ' : CoefCtx K V)
    (h : ∀ k ∈ S, σ k = σ' k) : satisfies σ S ↔ satisfies σ' S := by
  constructor <;> intro hs k hk
  · exact (CoefCtx.definedAt_iff σ' k).mpr (by
      rw [← h k hk]
      exact (CoefCtx.definedAt_iff σ k).mp (hs k hk))
  · exact (CoefCtx.definedAt_iff σ k).mpr (by
      rw [h k hk]
      exact (CoefCtx.definedAt_iff σ' k).mp (hs k hk))

/-! ## Definition 24: coeffects at a key -/

/-- **Definition 24.** An operation of the coeffect at key `k`: it carries an
argument type and an outcome type, and acts on the value alone, its first two
constituents forming an effect function on `V k`. -/
structure CoefOp (V : K → Type u) (k : K) where
  /-- The argument type. -/
  arg : Type v
  /-- The outcome type. -/
  out : Type v
  /-- The action: an effect function on `V k`. -/
  action : V k → V k × (V k → V k)

/-- **Definition 24.** A coeffect at a key `k`: the value type `V k`, an
equivalence `≃` up to which values at `k` are compared, and the operations
the bound value provides. -/
structure Coeffect (V : K → Type u) (k : K) where
  /-- The equivalence relation on `V k`. -/
  eqv : V k → V k → Prop
  /-- The operations the value bound at `k` provides. -/
  ops : List (CoefOp.{u, v} V k)

/-! ## Definitions 28–29: coeffect isolation -/

variable {R : Type} [DecidableEq R] [Inhabited R]

/-- **Definition 28.** The coeffect context with isolation:
`Σ^iso = (K ⇀ R) × ((k : K) ⇀ V_k)`: a realm table assigning realm
identifiers to isolated keys, together with a dependency table keyed by realm
identifiers. -/
abbrev IsoCtx (K : Type) (R : Type) (V : K → Type u) : Type _ :=
  CoefCtx K (fun _ => R) × CoefCtx R (fun _ => Σ' k : K, V k)

namespace IsoCtx

variable (σ : IsoCtx K R V)

/-- The realm a key resolves to: an isolated key resolves to its assigned
realm; a key outside the realm table resolves to its own realm
(`ρ ⊇ ≃`, Definition 28). -/
def realm (σ : IsoCtx K R V) (k : K) : R :=
  match σ.1 k with
  | some r => r
  | none => default

/-- **Definition 29.** `get` on `Σ^iso`: resolve `k` through the realm table,
then read the dependency table. -/
def get (σ : IsoCtx K R V) (k : K) (h : (σ.2 (σ.realm k)).isSome) :
    Σ' k' : K, V k' :=
  (σ.2 (σ.realm k)).get h

/-- **Definition 29.** `set (k, v)` on `Σ^iso`: bind the value at the key's
resolved realm; the inverse restricts at that realm. -/
def set (σ : IsoCtx K R V) (k : K) (v : V k) :
    IsoCtx K R V × (IsoCtx K R V → IsoCtx K R V) :=
  ((σ.1, CoefCtx.bind σ.2 (σ.realm k) ⟨k, v⟩),
    fun σ' => (σ'.1, CoefCtx.restrict σ'.2 (σ.realm k)))

/-- **Definition 29.** `isolate (k, r)` derives a context assigning realm `r`
to `k` and inheriting the dependency table unchanged; a key already isolated
is reassigned rather than refused (no precondition). -/
def isolate (σ : IsoCtx K R V) (k : K) (r : R) : IsoCtx K R V :=
  (CoefCtx.bind σ.1 k r, σ.2)

omit [DecidableEq R] in
/-- Isolation changes resolution: after `isolate (k, r)`, the key `k`
resolves to realm `r`. -/
theorem realm_isolate (σ : IsoCtx K R V) (k : K) (r : R) :
    (σ.isolate k r).realm k = r := by
  simp [realm, isolate, CoefCtx.bind]

end IsoCtx

/-! ## Definitions 30–31: coeffect interception -/

variable {M : K → Type v}

/-- **Definition 30.** The coeffect context with interception:
`Σ^inter = ((k : K) → M_k) × ((k : K) ⇀ (M_k → V_k))`: context-carried
metadata together with a provider table. -/
abbrev InterCtx (K : Type) (V : K → Type u) (M : K → Type v) : Type _ :=
    ((k : K) → M k) × CoefCtx K (fun k => M k → V k)

namespace InterCtx

variable (σ : InterCtx K V M)

/-- **Definition 31.** `get` on `Σ^inter`: the provider is applied to the
merge of the component-declared metadata with the context-carried metadata —
right-biased, so the context-carried metadata takes priority and can override
the component's declaration. -/
def get (σ : InterCtx K V M) (merge : (k : K) → M k → M k → M k)
    (k : K) (declared : M k) (h : (σ.2 k).isSome) : V k :=
  ((σ.2 k).get h) (merge k declared (σ.1 k))

/-- **Definition 31.** `set (k, p)` binds the provider `p` at `k`; the
inverse restricts the provider table at `k`. -/
def set (σ : InterCtx K V M) (k : K) (p : M k → V k) :
    InterCtx K V M × (InterCtx K V M → InterCtx K V M) :=
  ((σ.1, CoefCtx.bind σ.2 k p), fun σ' => (σ'.1, CoefCtx.restrict σ'.2 k))

/-- **Definition 31.** `intercept (k, m)` derives a context merging `m` onto
the metadata inherited at `k` and inheriting the provider table unchanged. -/
def intercept (σ : InterCtx K V M) (merge : (k : K) → M k → M k → M k)
    (k : K) (m : M k) : InterCtx K V M :=
  (fun k' => if h : k' = k then merge k' (h ▸ m) (σ.1 k') else σ.1 k', σ.2)

end InterCtx

end Cordix
