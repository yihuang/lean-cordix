import LeanCordix.Revertible
import LeanCordix.Coeffect

/-!
# Cordix — Section 4: A Calculus of Dynamic Composition

This module formalizes Section 4 of *A Programming Paradigm for Spatiotemporal
Composability* (Cordix/Cordis): the calculus of dynamic composition, in which
a system is decomposed into components, each pairing a coeffect specification
with a witnessed effect function, and an operational semantics drives their
lifecycle.

We formalize the **base calculus** of Section 4.2 (five rules, two-state
lifecycle, each transition atomic, immediate, and infallible) together with
the metatheory that the base calculus supports:

* Definition 43 — components `(S, P, τ)`.
* Definition 44 — fibers (the fields `c`, `p`, `σ`, `r`, `θ`).
* Definition 45 — the registry, and the coeffect context `Σ_γ` read off it
  (Eq. 40: the union of the tables of the active fibers).
* Definition 46 — target views and quiescence (Eqs. 41–42).
* The five rules of Section 4.2: `O-Insert`, `O-Retire`, `O-Remove`
  (orchestration) and `L-Reload`, `L-Unload` (lifecycle).
* Definition 50 — the withdrawal guard `relied` (used by the guarded
  calculus of Section 4.3.1).
* Definition 58 — well-formedness; **Theorem 59 (Preservation)** of clauses
  (1)–(2) under every base-calculus rule.
* **Theorem 63, first claim** (Ordering, Eq. 58): a fiber begins a
  transition only where its dependencies are provided.
* **Theorem 66, clause 1** (Progress / no deadlock) for the base calculus:
  a non-quiescent registry always admits a lifecycle step.

Not formalized here (future work): the ten-rule calculus of Section 4.3
(effect iterators, Definition 51; the guarded withdrawal of Section 4.3.1;
asynchrony; failure), the confinement discipline of Definition 48, and the
global metatheory of Section 4.4 that builds on those (recovery exactness,
resolution coherence, termination, confluence).  The paper notes that
clauses (3)–(4) of Definition 58 and Theorem 63 (2)–(3) belong to the
guarded calculus.

The ambient context: the paper's state `γ ∈ Γ∞` carries the registry together
with whatever else in `Γ` no fiber's table names (Definition 45).  We model
the registry with its per-fiber tables; the ambient remainder is transformed
by each fiber's effect function `τ` and recovered by its accumulator, exactly
as tracked by the machinery of `LeanCordix.Revertible` (Theorem 16), so the
rules below record the control-flow half of each transition and leave the
state map to Section 3.1.
-/

namespace Cordix

universe u

variable {N K : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Definition 43: components -/

/-- **Definition 43.** A component over a context carrying both effects and
coeffects: its coeffect side split into what it reads from the environment
(`spec`) and what it provides to it (`prov`), together with its witnessed
effect function. -/
structure Component (K : Type) (V : K → Type u) where
  /-- The coeffect specification `S`: the dependencies required from the
  environment. -/
  spec : Spec K
  /-- The provision `P`: the coeffect keys the component may provide. -/
  prov : List K
  /-- The effect function `τ`: the effects contributed when the component
  is active, together with the inverse that withdraws them. -/
  eff : Eff (CoefCtx K V)
  /-- The effect function is witnessed (Definition 8). -/
  wit : Witnessed eff

/-! ## Definitions 44–45: fibers and the registry -/

/-- **Definition 44 / Eq. 38.** The lifecycle state of a fiber in the
two-state model: inactive, or active carrying the accumulator `κ` and the
committed view `v`. -/
inductive Lifecycle (N : Type) (K : Type) (V : K → Type u)
  | inactive : Lifecycle N K V
  | active (acc : CoefCtx K V → CoefCtx K V) (view : K → Option N) :
    Lifecycle N K V

/-- A fiber is installed when it is in a lifecycle state carrying a
committed view. -/
def Lifecycle.installed {N K : Type} {V : K → Type u} :
    Lifecycle N K V → Prop
  | .active _ _ => True
  | .inactive => False

/-- The committed view of a lifecycle state (the trivial one when
inactive). -/
def Lifecycle.viewOf {N K : Type} {V : K → Type u} :
    Lifecycle N K V → K → Option N
  | .active _ v => v
  | .inactive => fun _ => none

/-- **Definition 44.** A fiber instantiating a component: the component
triple, the parent (the fiber this one was instantiated under, `none` for the
root marker `⊤`), the fiber's own coeffect table, the retirement flag, and
the lifecycle state. -/
structure Fiber (N : Type) (K : Type) (V : K → Type u) where
  /-- The component `(S, P, τ)` the fiber instantiates. -/
  comp : Component K V
  /-- The parent `p`, or `none` for the root marker. -/
  parent : Option N
  /-- The fiber's own coeffect table `σ`, empty until it activates and
  written by its effects as they run. -/
  table : CoefCtx K V
  /-- The retirement flag `r`, `false` in a fresh fiber. -/
  retired : Bool
  /-- The lifecycle state `θ`. -/
  lc : Lifecycle N K V

/-- **Definition 45.** The registry: a finite partial function from fiber
names to fibers (an association list taking the frontmost entry). -/
abbrev Registry (N K : Type) (V : K → Type u) := List (N × Fiber N K V)

/-- Lookup in a registry. -/
def regLookup {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} :
    Registry N K V → N → Option (Fiber N K V)
  | [], _ => none
  | p :: rest, n => if p.1 = n then some p.2 else regLookup rest n

/-- Pointwise update: write the fiber at a name (fresh if absent); lookup
takes the frontmost entry, so the semantics is that of a partial map. -/
def regSet (r : Registry N K V) (n : N) (f : Fiber N K V) : Registry N K V :=
  (n, f) :: r

/-- Removal: drop the fiber at a name (all of its entries). -/
def regDel : Registry N K V → N → Registry N K V
  | [], _ => []
  | p :: rest, n => if p.1 = n then regDel rest n else p :: regDel rest n

omit [DecidableEq K] in
theorem regLookup_set_eq (r : Registry N K V) (n : N) (f : Fiber N K V) :
    regLookup (regSet r n f) n = some f := by
  show (if n = n then some f else _) = some f
  rw [if_pos rfl]

omit [DecidableEq K] in
theorem regLookup_set_ne (r : Registry N K V) (n m : N) (f : Fiber N K V)
    (hne : m ≠ n) :
    regLookup (regSet r n f) m = regLookup r m := by
  show (if n = m then some f else _) = _
  rw [if_neg (fun e => hne e.symm)]

omit [DecidableEq K] in
theorem lookup_del_none (m : N) :
    ∀ r : Registry N K V, regLookup (regDel r m) m = none
  | [] => rfl
  | p :: rest => by
    by_cases h : p.1 = m
    · show regLookup (if p.1 = m then regDel rest m else _) m = none
      rw [if_pos h]
      exact lookup_del_none m rest
    · show regLookup (if p.1 = m then regDel rest m else _) m = none
      rw [if_neg h]
      show (if p.1 = m then some p.2 else regLookup (regDel rest m) m) = none
      rw [if_neg h]
      exact lookup_del_none m rest

omit [DecidableEq K] in
theorem regLookup_del (r : Registry N K V) (n m : N) (hne : m ≠ n) :
    regLookup (regDel r n) m = regLookup r m := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
    show regLookup (if p.1 = n then regDel rest n else p :: regDel rest n) m
        = (if p.1 = m then some p.2 else regLookup rest m)
    by_cases h : p.1 = n
    · rw [if_pos h]
      by_cases hm : p.1 = m
      · exact absurd (h.symm.trans hm).symm hne
      · rw [if_neg hm]
        exact ih
    · rw [if_neg h]
      show (if p.1 = m then some p.2 else regLookup (regDel rest n) m) = _
      by_cases hm : p.1 = m
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm]
        exact ih

omit [DecidableEq K] in
theorem regLookup_del_self (r : Registry N K V) (n : N) :
    regLookup (regDel r n) n = none :=
  lookup_del_none n r

/-- **Definition 45 / Eq. 40.** The coeffect context of the state: the union
of the tables of the active fibers. -/
def sigmaOf (r : Registry N K V) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => p.2.table k <|> acc
    | .inactive => acc

/-- The provider of a key: the active fiber whose table defines it. -/
def providerOf (r : Registry N K V) (k : K) : Option N :=
  r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => if (p.2.table k).isSome then some p.1 else acc
    | .inactive => acc

/-! ## Definition 46: target views and quiescence -/

/-- **Definition 46 / Eq. 41.** The target view of `n` at `r`: `⊥` (here
`none`) when the fiber ought not be running at all — retired, or its
specification unsatisfied — and otherwise the map sending each declared key
to its provider. -/
noncomputable def targetOf (r : Registry N K V) (n : N) :
    Option (K → Option N) :=
  match regLookup r n with
  | some f =>
    if f.retired = true ∨ ¬satisfies (sigmaOf r) f.comp.spec then none
    else some (providerOf r)
  | none => none

/-- **Definition 46 / Eq. 42.** A state is quiescent when every fiber has
reached its target view. -/
def quiet (r : Registry N K V) : Prop :=
  ∀ n f, regLookup r n = some f →
    match f.lc with
    | .inactive => targetOf r n = none
    | .active _ v => targetOf r n = some v

/-! ## Definition 50: the withdrawal guard -/

/-- **Definition 50.** The fiber `n` is relied upon when some other
installed fiber resolves a key to it.  (The guarded calculus of Section 4.3.1
adds `¬relied r n` as the premise of `L-Unload`, holding a provider's
withdrawal back until every consumer that resolves to it has gone.) -/
def relied (r : Registry N K V) (n : N) : Prop :=
  ∃ n' k f, regLookup r n' = some f ∧ n' ≠ n ∧ f.lc.installed
    ∧ f.lc.viewOf k = some n

/-! ## Section 4.2: the rules -/

/-- The orchestration rules `O-*`: actions the orchestrator may perform.
Their premises say when the action is legal, not when it occurs. -/
inductive Ostep : Registry N K V → Registry N K V → Prop
  /-- `O-Insert`: introduce a fiber for the component `c` at a fresh name,
  under parent `p`; the single-source discipline requires the new provision
  to be disjoint from every present one. -/
  | oInsert (r : Registry N K V) (n : N) (c : Component K V) (p : Option N)
      (hn : regLookup r n = none)
      (hp : ∀ n' ∈ p, ∃ f, regLookup r n' = some f)
      (hdisj : ∀ n' f, regLookup r n' = some f →
        (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
      Ostep r (regSet r n ⟨c, p, fun _ => none, false, .inactive⟩)
  /-- `O-Retire`: mark the fiber at `n` retired.  Unconditional on the
  fiber's state: retiring is a request, and the lifecycle rules carry it
  out. -/
  | oRetire (r : Registry N K V) (n : N) (f : Fiber N K V)
      (h : regLookup r n = some f) :
      Ostep r (regSet r n { f with retired := true })
  /-- `O-Remove`: drop the fiber at `n` outright.  Only an inactive fiber
  may be removed (removing earlier would discard the accumulator and leak),
  and children must be removed before their parent. -/
  | oRemove (r : Registry N K V) (n : N) (f : Fiber N K V)
      (hl : f.lc = .inactive)
      (hchild : ∀ n' f', regLookup r n' = some f' → f'.parent ≠ some n) :
      Ostep r (regDel r n)

/-- The lifecycle rules `L-*`: steps the system takes unprompted whenever
their premises hold. -/
inductive Lstep : Registry N K V → Registry N K V → Prop
  /-- `L-Reload`: install the committed view `v` alongside the inverse
  `κ = pr₂ (τ (Σ_γ))` that the effect function yields where the transition
  commits. -/
  | lReload (r : Registry N K V) (n : N) (f : Fiber N K V) (v : K → Option N)
      (κ : CoefCtx K V → CoefCtx K V)
      (hf : regLookup r n = some f)
      (hl : f.lc = .inactive)
      (ht : targetOf r n = some v)
      (hκ : κ = (f.comp.eff (sigmaOf r)).2) :
      Lstep r (regSet r n { f with lc := .active κ v })
  /-- `L-Unload`: apply the accumulator and discard the committed view.
  (Section 4.3.1 splits this into `L-Leave` and a guarded `L-Unload`.) -/
  | lUnload (r : Registry N K V) (n : N) (f : Fiber N K V)
      (κ : CoefCtx K V → CoefCtx K V) (v : K → Option N)
      (hf : regLookup r n = some f)
      (hl : f.lc = .active κ v)
      (ht : targetOf r n ≠ some v) :
      Lstep r (regSet r n { f with lc := .inactive })

/-! ## Theorem 63, first claim: ordering -/

omit [DecidableEq K] in
/-- **Theorem 63 (Eq. 58).** A fiber begins a transition only where its
dependencies are provided: the premise `target ≠ ⊥` of `L-Reload` gives
`Σ_γ ⊨ S` (and `¬retired`). -/
theorem satisfies_of_lReload {r : Registry N K V} {n : N} {v : K → Option N}
    (ht : targetOf r n = some v) :
    ∃ g : Fiber N K V, regLookup r n = some g ∧ ¬ g.retired
      ∧ satisfies (sigmaOf r) g.comp.spec := by
  unfold targetOf at ht
  cases hl : regLookup r n with
  | none => rw [hl] at ht; exact absurd ht (by simp)
  | some g =>
    rw [hl] at ht
    simp only [] at ht
    by_cases hc : g.retired = true ∨ ¬satisfies (sigmaOf r) g.comp.spec
    · rw [if_pos hc] at ht; exact absurd ht (by simp)
    · rw [if_neg hc] at ht
      refine ⟨g, rfl, fun hret => hc (Or.inl hret),
        Classical.byContradiction fun hsat => hc (Or.inr hsat)⟩

/-! ## Definition 58: well-formedness -/

/-- **Definition 58.** A registry is well formed when (1) every parent
pointer lands in the registry, and (2) the provisions of distinct fibers are
disjoint (the single-source discipline: each key has one possible provider,
fixed by the provisions and not by the state).  Clauses (3)–(4), on committed
views, are established by the guarded calculus of Section 4.3.1. -/
structure WellFormed (r : Registry N K V) : Prop where
  /-- Clause (1): the parent tree, read one edge at a time. -/
  parentOk : ∀ n f, regLookup r n = some f → ∀ m ∈ f.parent,
    ∃ f', regLookup r m = some f'
  /-- Clause (2): disjointness of provisions. -/
  provDisj : ∀ n f n' f', regLookup r n = some f → regLookup r n' = some f' →
    n ≠ n' → ∀ k ∈ f.comp.prov, ∀ k' ∈ f'.comp.prov, k ≠ k'

/-! ## Transfer helpers -/

omit [DecidableEq K] in
/-- Lookup after pointwise update, for the well-formedness transfer. -/
theorem regLookup_set_cases {r : Registry N K V} {n m : N}
    {f f' : Fiber N K V}
    (h : regLookup (regSet r n f) m = some f') :
    (m = n ∧ f' = f) ∨ (m ≠ n ∧ regLookup r m = some f') := by
  by_cases hmn : m = n
  · refine .inl ⟨hmn, ?_⟩
    rw [hmn, regLookup_set_eq] at h
    exact (Option.some.inj h).symm
  · refine .inr ⟨hmn, ?_⟩
    rw [regLookup_set_ne r n m f hmn] at h
    exact h

omit [DecidableEq K] in
/-- Lookup after removal never hits the removed name. -/
theorem regLookup_del_cases {r : Registry N K V} {n m : N} {f' : Fiber N K V}
    (h : regLookup (regDel r n) m = some f') :
    m ≠ n ∧ regLookup r m = some f' := by
  refine ⟨fun hmn => by rw [hmn, regLookup_del_self] at h; simp at h, ?_⟩
  by_cases hmn : m = n
  · rw [hmn, regLookup_del_self] at h; simp at h
  · rw [regLookup_del r n m hmn] at h; exact h

/-! ## Theorem 59: preservation -/

omit [DecidableEq K] in
/-- Well-formedness is preserved by a pointwise update at an *existing*
name, when the update preserves the component and the parent (as
`O-Retire`, `L-Reload`, and `L-Unload` do). -/
theorem wellFormed_set (hwf : WellFormed r) {n : N} {old new : Fiber N K V}
    (h : regLookup r n = some old) (hc : old.comp = new.comp)
    (hp : old.parent = new.parent) : WellFormed (regSet r n new) := by
  constructor
  · intro m g hm x hx
    obtain ⟨g₂, hg₂⟩ : ∃ g₂, regLookup r x = some g₂ := by
      rcases regLookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact hwf.parentOk n old h x (hp.symm ▸ (hg ▸ hx))
      · exact hwf.parentOk m g hg x hx
    by_cases hxn : x = n
    · subst hxn
      exact ⟨new, regLookup_set_eq r _ new⟩
    · rw [regLookup_set_ne r n x new hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    have toR : ∀ a α (ha : regLookup (regSet r n new) a = some α),
        ∃ β, regLookup r a = some β ∧ β.comp = α.comp := by
      intro a α ha
      rcases regLookup_set_cases ha with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · subst heq; subst hg
        exact ⟨old, h, hc⟩
      · exact ⟨α, hg, rfl⟩
    obtain ⟨β, hb, hβ⟩ := toR m g hm
    obtain ⟨β', hb', hβ'⟩ := toR m' g' hm'
    have hk₁ : k ∈ β.comp.prov := by rw [hβ]; exact hk
    have hk₂ : k' ∈ β'.comp.prov := by rw [hβ']; exact hk'
    exact hwf.provDisj m β m' β' hb hb' hne k hk₁ k' hk₂

omit [DecidableEq K] in
/-- Well-formedness is preserved by a pointwise update at a *fresh* name. -/
theorem wellFormed_setFresh (hwf : WellFormed r) {n : N} {c : Component K V}
    {p : Option N} {fresh : Fiber N K V}
    (hnone : regLookup r n = none) (hcomp : fresh.comp = c)
    (hpar : fresh.parent = p)
    (hp : ∀ x ∈ p, ∃ g, regLookup r x = some g)
    (hdisj : ∀ m g, regLookup r m = some g →
      ∀ k ∈ c.prov, ∀ k' ∈ g.comp.prov, k ≠ k') :
    WellFormed (regSet r n fresh) := by
  constructor
  · intro m g hm x hx
    have hgr : regLookup r m = some g ∨ (m = n ∧ g = fresh) := by
      rcases regLookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact .inr ⟨heq, hg⟩
      · exact .inl hg
    have hland : ∃ g₂, regLookup r x = some g₂ := by
      rcases hgr with hg | ⟨heq, hg⟩
      · exact hwf.parentOk m g hg x hx
      · subst heq; subst hg
        rw [hpar] at hx
        exact hp x hx
    obtain ⟨g₂, hg₂⟩ := hland
    by_cases hxn : x = n
    · subst hxn
      exact ⟨fresh, regLookup_set_eq r _ fresh⟩
    · rw [regLookup_set_ne r n x fresh hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    by_cases hmn : m = n
    · rw [hmn, regLookup_set_eq] at hm
      have hgf : g = fresh := (Option.some.inj hm).symm
      rw [hgf, hcomp] at hk
      have hg' : regLookup r m' = some g' := by
        rcases regLookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd (hmn.trans heq.symm) hne
        · exact hg
      exact hdisj m' g' hg' k hk k' hk'
    · have hmOld : regLookup r m = some g := by
        rcases regLookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd heq hmn
        · exact hg
      by_cases hmn' : m' = n
      · rw [hmn', regLookup_set_eq] at hm'
        have hgf : g' = fresh := (Option.some.inj hm').symm
        rw [hgf, hcomp] at hk'
        exact fun heq => hdisj m g hmOld k' hk' k hk heq.symm
      · have hmOld' : regLookup r m' = some g' := by
          rcases regLookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
          · exact absurd heq hmn'
          · exact hg
        exact hwf.provDisj m g m' g' hmOld hmOld' hne k hk k' hk'

/-- Well-formedness is preserved by removal, given no fiber points at the
removed name. -/
theorem wellFormed_del (hwf : WellFormed r) {n : N}
    (hchild : ∀ m g, regLookup r m = some g → g.parent ≠ some n) :
    WellFormed (regDel r n) := by
  constructor
  · intro m g hm x hx
    obtain ⟨hne, hg⟩ := regLookup_del_cases hm
    obtain ⟨g₂, hg₂⟩ := hwf.parentOk m g hg x hx
    have hxn : x ≠ n := by
      intro heq; subst heq
      simp only [Option.mem_def] at hx
      exact hchild m g hg hx
    rw [regLookup_del r n x hxn]
    exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    obtain ⟨_, hg⟩ := regLookup_del_cases hm
    obtain ⟨_, hg'⟩ := regLookup_del_cases hm'
    exact hwf.provDisj m g m' g' hg hg' hne k hk k' hk'

omit [DecidableEq K] in
/-- **Theorem 59 (Preservation), clauses (1)–(2).**  If `r` is well formed
then so is the registry any base-calculus rule step reaches. -/
theorem WellFormed.preserved {r r' : Registry N K V} (hwf : WellFormed r)
    (h : Ostep r r' ∨ Lstep r r') : WellFormed r' := by
  rcases h with h | h
  · cases h with
    | oInsert _ _ _ hn hp hdisj => exact wellFormed_setFresh hwf hn rfl rfl hp hdisj
    | oRetire _ _ h => exact wellFormed_set hwf h rfl rfl
    | oRemove _ _ hl hchild => exact wellFormed_del hwf hchild
  · cases h with
    | lReload _ _ _ _ hf _ _ _ => exact wellFormed_set hwf hf rfl rfl
    | lUnload _ _ _ _ hf _ _ => exact wellFormed_set hwf hf rfl rfl

/-! ## Theorem 66, clause 1: progress (no deadlock) -/

omit [DecidableEq K] in
/-- **Theorem 66 (no deadlock), base calculus.**  A registry that is not
quiescent admits a lifecycle step. -/
theorem exists_lstep_of_not_quiet {r : Registry N K V} (h : ¬ quiet r) :
    ∃ r', Lstep r r' := by
  have hex : ∃ n f, regLookup r n = some f ∧ ¬ (match f.lc with
    | .inactive => targetOf r n = none
    | .active _ v => targetOf r n = some v) := by
    refine Classical.byContradiction fun hc => h ?_
    intro n f hl
    by_cases hh : (match f.lc with
      | .inactive => targetOf r n = none
      | .active _ v => targetOf r n = some v)
    · exact hh
    · exact absurd ⟨n, f, hl, hh⟩ hc
  obtain ⟨n, f, hf, hnot⟩ := hex
  cases hlc : f.lc with
  | inactive =>
    rw [hlc] at hnot
    cases ht : targetOf r n with
    | none => exact absurd ht hnot
    | some v => exact ⟨_, Lstep.lReload r n f v _ hf hlc ht rfl⟩
  | active κ v =>
    rw [hlc] at hnot
    exact ⟨_, Lstep.lUnload r n f κ v hf hlc hnot⟩

end Cordix
