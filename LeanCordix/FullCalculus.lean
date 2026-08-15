import LeanCordix.Iterator
import LeanCordix.Coeffect

/-!
# Cordix — Section 4.3/4.4: The Full Calculus of Dynamic Composition

This module formalizes the full ten-rule calculus of Section 4.3, together
with the beginning of the metatheory of Section 4.4.  The base two-state
calculus of Section 4.2 lives in `LeanCordix.Calculus`; here the lifecycle
has the four states of Definition 49:

`inactive o` — not installed, carrying the outcome `o` it reached
  (`none` for a normal unload, `some e` after a failure);
`loading ι κ v` — an activation in progress, carrying the remaining effect
  iterator `ι`, the accumulator `κ` built so far, and the committed view `v`;
`active κ v` — installed and providing its table;
`unloading κ v o` — a deactivation in progress, carrying the accumulator to
  be applied, the committed view that is still visible, and the outcome the
  fiber is headed for.

The rules are the ten of Section 4.3: the three orchestration rules, the
activation rules `L-Begin`, `L-Iter`, `L-Finish`, the early exits `L-Divert`
(abort and landing) and `L-Raise`, and the deactivation rules `L-Leave` and
`L-Unload`.  We model the registry by a list of named fibers, exactly as the
base calculus does, but use a proper pointwise update (`set` replaces the
first entry at a name instead of prepending a shadowing one) so that
`NodupKeys` is preserved by the rules.
-/

namespace Cordix

namespace Full

set_option linter.unusedSectionVars false

universe u v

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Components and fibers -/

/-- **Definition 43 / Section 4.3.** A component over the coeffect context:
its specification, its provision, and its witnessed effect iterator. -/
structure Component (K : Type) (V : K → Type u) (E : Type) where
  /-- The dependencies required from the environment. -/
  spec : Spec K
  /-- The keys the component may provide. -/
  prov : List K
  /-- The effect iterator executed on activation. -/
  iter : Iterator (CoefCtx K V) E
  /-- The iterator is witnessed (Definition 51 / Eq. 49). -/
  wit : Iterator.Witnessed iter

/-- **Definition 49.** The lifecycle state of a fiber in the full calculus. -/
inductive Lifecycle (N : Type) (K : Type) (V : K → Type u) (E : Type)
  | inactive (outcome : Option E) : Lifecycle N K V E
  | loading (iter : Iterator (CoefCtx K V) E) (acc : CoefCtx K V → CoefCtx K V)
      (view : K → Option N) : Lifecycle N K V E
  | active (acc : CoefCtx K V → CoefCtx K V) (view : K → Option N) :
      Lifecycle N K V E
  | unloading (acc : CoefCtx K V → CoefCtx K V) (view : K → Option N)
      (outcome : Option E) : Lifecycle N K V E

namespace Lifecycle

/-- **Definition 49 / Eq. 44.** A fiber is installed when it is not in an
`inactive` state; installed fibers carry an accumulator and a committed
view. -/
def installed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive _ => False
  | .loading _ _ _ => True
  | .active _ _ => True
  | .unloading _ _ _ => True

/-- The committed view of a lifecycle state; `none` for inactive fibers. -/
def viewOf {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → K → Option N
  | .inactive _ => fun _ => none
  | .loading _ _ v => v
  | .active _ v => v
  | .unloading _ v _ => v

/-- **Definition 49 / Eq. 44.** A fiber is failed when it has reached an
error outcome. -/
def failed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive (some _) => True
  | _ => False

/-- `inactive none`: the state a fresh fiber is inserted in and the state a
normal unload reaches. -/
abbrev fresh {N K : Type} {V : K → Type u} {E : Type} : Lifecycle N K V E :=
  .inactive none

end Lifecycle

/-- **Definition 44.** A fiber in the full calculus. -/
structure Fiber (N : Type) (K : Type) (V : K → Type u) (E : Type) where
  comp : Component K V E
  parent : Option N
  table : CoefCtx K V
  retired : Bool
  lc : Lifecycle N K V E

/-- **Definition 45.** The registry: a list of named fibers. -/
abbrev Registry (N K : Type) (V : K → Type u) (E : Type) :=
  List (N × Fiber N K V E)

/-! ## Registry operations -/

/-- Lookup in a registry. -/
def lookup {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Option (Fiber N K V E)
  | [], _ => none
  | p :: rest, n => if p.1 = n then some p.2 else lookup rest n

/-- Pointwise update: replace the first entry at `n`, or append the new
entry when `n` is absent.  This is the proper finite-function update. -/
def set {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Fiber N K V E → Registry N K V E
  | [], n, f => [(n, f)]
  | p :: rest, n, f =>
      if p.1 = n then (n, f) :: rest else p :: set rest n f

/-- Removal: drop all entries at `n`. -/
def del {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Registry N K V E
  | [], _ => []
  | p :: rest, n => if p.1 = n then del rest n else p :: del rest n

omit [DecidableEq K] in
theorem lookup_set_eq (r : Registry N K V E) (n : N) (f : Fiber N K V E) :
    lookup (set r n f) n = some f := by
  induction r with
  | nil => simp [set, lookup]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · simp [set, lookup, h]
      · simp [set, lookup, h, ih]

omit [DecidableEq K] in
theorem lookup_set_ne (r : Registry N K V E) (n m : N) (f : Fiber N K V E)
    (hne : m ≠ n) : lookup (set r n f) m = lookup r m := by
  induction r with
  | nil => simp [set, lookup, Ne.symm hne]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · rw [show set (p :: rest) n f = (n, f) :: rest by simp [set, h]]
        rw [show lookup (p :: rest) m = if n = m then some p.snd else lookup rest m by
          simp [lookup, h]]
        simp [lookup, Ne.symm hne]
      · by_cases hm : p.1 = m
        · rw [show set (p :: rest) n f = p :: set rest n f by simp [set, h]]
          simp [lookup, hm]
        · rw [show set (p :: rest) n f = p :: set rest n f by simp [set, h]]
          simp [lookup, hm, ih]

omit [DecidableEq K] in
theorem lookup_set_cases {r : Registry N K V E} {n m : N}
    {f f' : Fiber N K V E} (h : lookup (set r n f) m = some f') :
    (m = n ∧ f' = f) ∨ (m ≠ n ∧ lookup r m = some f') := by
  by_cases hmn : m = n
  · left
    subst hmn
    rw [lookup_set_eq] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · right
    exact ⟨hmn, by rwa [lookup_set_ne r n m f hmn] at h⟩

omit [DecidableEq K] in
theorem lookup_del_self (n : N) :
    ∀ r : Registry N K V E, lookup (del r n) n = none
  | [] => rfl
  | p :: rest => by
      by_cases h : p.1 = n
      · rw [show del (p :: rest) n = del rest n by simp [del, h]]
        exact lookup_del_self n rest
      · rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        simp [lookup, h]
        exact lookup_del_self n rest

omit [DecidableEq K] in
theorem lookup_del_ne (r : Registry N K V E) (n m : N) (hne : m ≠ n) :
    lookup (del r n) m = lookup r m := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases h : p.1 = n
      · rw [show del (p :: rest) n = del rest n by simp [del, h]]
        by_cases hm : p.1 = m
        · exfalso
          exact hne (h.symm.trans hm).symm
        · have hnm : ¬ n = m := by
            intro hn
            exact hm (h.trans hn)
          simp [lookup, h, hnm]
          exact ih
      · rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        by_cases hm : p.1 = m
        · simp [lookup, hm]
        · simp [lookup, hm, ih]

omit [DecidableEq K] in
theorem lookup_del_cases {r : Registry N K V E} {n m : N} {f' : Fiber N K V E}
    (h : lookup (del r n) m = some f') :
    m ≠ n ∧ lookup r m = some f' := by
  refine ⟨fun hmn => by rw [hmn, lookup_del_self] at h; simp at h, ?_⟩
  by_cases hmn : m = n
  · rw [hmn, lookup_del_self] at h; simp at h
  · rwa [lookup_del_ne r n m hmn] at h

/-- The names of a registry are duplicate-free. -/
def NodupKeys (r : Registry N K V E) : Prop :=
  List.Nodup (r.map (fun p => p.1))

/-- The pointwise update does not add old keys under new names. -/
theorem key_not_mem_set {r : Registry N K V E} {n : N} {f : Fiber N K V E} {p : N}
    (hn : p ∉ r.map (fun q => q.1)) (hp : p ≠ n) :
    p ∉ (set r n f).map (fun q => q.1) := by
  revert hn
  induction r with
  | nil =>
      intro hn h
      simp [set] at h
      exact hp h
  | cons q rest ih =>
      intro hn h
      by_cases hq : q.1 = n
      · simp [set, hq] at h
        rcases h with hEq | hIn
        · exact hp hEq
        · have hnq : p ∉ rest.map (fun q => q.1) := by
            intro h'
            exact hn (by simp [h'])
          have hIn' : p ∈ rest.map (fun q => q.1) := by
            rw [List.mem_map]
            rcases hIn with ⟨x, hx⟩
            exact ⟨(p, x), hx, rfl⟩
          exact absurd hIn' hnq
      · simp [set, hq] at h
        rcases h with hEq | hIn
        · exact hn (by simp [hEq])
        · have hnq : p ∉ rest.map (fun q => q.1) := by
            intro h'
            exact hn (by simp [h'])
          exact ih hnq (by
            rw [List.mem_map]
            rcases hIn with ⟨x, hx⟩
            exact ⟨(p, x), hx, rfl⟩)

/-- Removal does not introduce old keys. -/
theorem key_not_mem_del {r : Registry N K V E} {n : N} {p : N}
    (hn : p ∉ r.map (fun q => q.1)) :
    p ∉ (del r n).map (fun q => q.1) := by
  revert hn
  induction r with
  | nil =>
      intro hn h
      simp [del] at h
  | cons q rest ih =>
      intro hn h
      by_cases hq : q.1 = n
      · rw [show del (q :: rest) n = del rest n by simp [del, hq]] at h
        have hnq : p ∉ rest.map (fun q => q.1) := by
          intro h'
          exact hn (by simp [h'])
        exact ih hnq h
      · simp [del, hq] at h
        rcases h with hEq | hIn
        · exact hn (by simp [hEq])
        · have hnq : p ∉ rest.map (fun q => q.1) := by
            intro h'
            exact hn (by simp [h'])
          exact ih hnq (by
            rw [List.mem_map]
            rcases hIn with ⟨x, hx⟩
            exact ⟨(p, x), hx, rfl⟩)

/-- The pointwise update preserves duplicate-free names. -/
theorem nodupKeys_set (r : Registry N K V E) (n : N) (f : Fiber N K V E)
    (hn : NodupKeys r) : NodupKeys (set r n f) := by
  induction r with
  | nil => simp [set, NodupKeys]
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · subst n
        simp [set]
        change (p.1 :: rest.map (fun q => q.1)).Nodup
        change (p.1 :: rest.map (fun q => q.1)).Nodup at hn
        exact hn
      · simp [set, hp]
        change ((p.1 :: (set rest n f).map (fun q => q.1)).Nodup)
        rw [List.nodup_cons]
        change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        rcases hn with ⟨hnmem, hnrest⟩
        constructor
        · exact key_not_mem_set hnmem hp
        · exact ih hnrest

/-- Removal preserves duplicate-free names. -/
theorem nodupKeys_del (r : Registry N K V E) (n : N) (hn : NodupKeys r) :
    NodupKeys (del r n) := by
  induction r with
  | nil => simp [del, NodupKeys]
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · simp [del, hp]
        change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        exact ih hn.2
      · simp [del, hp]
        change ((p.1 :: (del rest n).map (fun q => q.1)).Nodup)
        rw [List.nodup_cons]
        change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        rcases hn with ⟨hnmem, hnrest⟩
        constructor
        · exact key_not_mem_del hnmem
        · exact ih hnrest

/-! ## Derived context and target view -/

/-- **Definition 45 / Eq. 40.** The coeffect context of a state: the union
of the tables of the `active` fibers alone. -/
def sigmaOf (r : Registry N K V E) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => p.2.table k <|> acc
    | _ => acc

/-- The provider of a key: the active fiber whose table defines it. -/
def providerOf (r : Registry N K V E) (k : K) : Option N :=
  r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => if (p.2.table k).isSome then some p.1 else acc
    | _ => acc

/-- **Definition 46 / Eq. 41.** The target view of `n` at `r`. -/
noncomputable def targetOf (r : Registry N K V E) (n : N) :
    Option (K → Option N) :=
  match lookup r n with
  | some f =>
      if f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec then none
      else some (fun k => if k ∈ f.comp.spec then providerOf r k else none)
  | none => none

/-- **Definition 49 / Eq. 45.** Quiescence in the full calculus. -/
def quiet (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f →
    match f.lc with
    | .inactive o => o ≠ none ∨ targetOf r n = none
    | .loading _ _ _ => False
    | .active _ v => targetOf r n = some v
    | .unloading _ _ _ => False

/-- **Definition 50.** The fiber `n` is relied upon when some other
installed fiber resolves a key to it. -/
def relied (r : Registry N K V E) (n : N) : Prop :=
  ∃ n' k f, lookup r n' = some f ∧ n' ≠ n ∧ f.lc.installed
    ∧ f.lc.viewOf k = some n

/-! ## The ten rules -/

/-- The orchestration rules `O-*`. -/
inductive Ostep : Registry N K V E → Registry N K V E → Prop
  | oInsert (r : Registry N K V E) (n : N) (c : Component K V E) (p : Option N)
      (hn : lookup r n = none)
      (hp : ∀ n' ∈ p, ∃ f, lookup r n' = some f)
      (hdisj : ∀ n' f, lookup r n' = some f →
        (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
      Ostep r (set r n ⟨c, p, fun _ => none, false, .inactive none⟩)
  | oRetire (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (h : lookup r n = some f) :
      Ostep r (set r n { f with retired := true })
  | oRemove (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (o : Option E) (h : lookup r n = some f) (hl : f.lc = .inactive o)
      (hchild : ∀ n' f', lookup r n' = some f' → f'.parent ≠ some n) :
      Ostep r (del r n)

/-- The lifecycle rules `L-*`. -/
inductive Lstep : Registry N K V E → Registry N K V E → Prop
  | lBegin (r : Registry N K V E) (n : N) (f : Fiber N K V E) (v : K → Option N)
      (hf : lookup r n = some f) (hl : f.lc = .inactive none)
      (ht : targetOf r n = some v) :
      Lstep r (set r n { f with lc := .loading f.comp.iter id v })
  | lIter (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (ι' : Iterator (CoefCtx K V) E)
      (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf r n = some v)
      (hstep : Iterator.step ι (sigmaOf r) = .ok (δ, h, some ι')) :
      Lstep r (set r n { f with lc := .loading ι' (κ ∘ h) v })
  | lFinish (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf r n = some v)
      (hstep : Iterator.step ι (sigmaOf r) = .ok (δ, h, none)) :
      Lstep r (set r n { f with lc := .active (κ ∘ h) v })
  | lRaise (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (e : E)
      (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
      (hstep : Iterator.step ι (sigmaOf r) = .error e) :
      Lstep r (set r n { f with lc := .unloading κ v (some e) })
  | lDivertAbort (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N)
      (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf r n ≠ some v) :
      Lstep r (set r n { f with lc := .unloading κ v none })
  | lDivertLand (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (c : Option (Iterator (CoefCtx K V) E))
      (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf r n ≠ some v)
      (hstep : Iterator.step ι (sigmaOf r) = .ok (δ, h, c)) :
      Lstep r (set r n { f with lc := .unloading (κ ∘ h) v none })
  | lLeave (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (κ : CoefCtx K V → CoefCtx K V) (v : K → Option N)
      (hf : lookup r n = some f) (hl : f.lc = .active κ v)
      (ht : targetOf r n ≠ some v) :
      Lstep r (set r n { f with lc := .unloading κ v none })
  | lUnload (r : Registry N K V E) (n : N) (f : Fiber N K V E)
      (κ : CoefCtx K V → CoefCtx K V) (v : K → Option N) (o : Option E)
      (hf : lookup r n = some f) (hl : f.lc = .unloading κ v o)
      (hg : ¬ relied r n) :
      Lstep r (set r n { f with lc := .inactive o })

/-! ## Basic consequences of the rules -/

/-- **Theorem 63 (Eq. 58), full calculus.** A fiber begins a transition
only where its dependencies are provided: `target ≠ ⊥` gives a live,
unsatisfied? (actually satisfied) specification and a non-retired fiber. -/
theorem satisfies_of_target {r : Registry N K V E} {n : N} {v : K → Option N}
    (ht : targetOf r n = some v) :
    ∃ f : Fiber N K V E, lookup r n = some f ∧ ¬ f.retired = true
      ∧ satisfies (sigmaOf r) f.comp.spec := by
  unfold targetOf at ht
  cases hl : lookup r n with
  | none => rw [hl] at ht; exact absurd ht (by simp)
  | some f =>
      rw [hl] at ht
      simp only [] at ht
      by_cases hc : f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec
      · rw [if_pos hc] at ht; exact absurd ht (by simp)
      · rw [if_neg hc] at ht
        refine ⟨f, rfl, fun hret => hc (Or.inl hret),
          Classical.byContradiction fun hsat => hc (Or.inr hsat)⟩

/-! ## Lemmas about `sigmaOf` and `providerOf` -/

/-- If the coeffect context provides a key, then some active fiber is its
provider. -/
theorem providerOf_isSome_of_sigmaOf_isSome {r : Registry N K V E} {k : K} :
    (sigmaOf r k).isSome → (providerOf r k).isSome := by
  induction r with
  | nil => simp [sigmaOf, providerOf]
  | cons p rest ih =>
      intro h
      cases hlc : p.2.lc with
      | inactive _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)
      | loading _ _ _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)
      | active _ _ =>
          by_cases htbl : (p.2.table k).isSome
          · simp [providerOf, hlc, htbl]
          · simpa [providerOf, hlc, htbl] using ih (by simpa [sigmaOf, hlc, htbl] using h)
      | unloading _ _ _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)

/-- The name returned by `providerOf` is a key of the registry. -/
theorem providerOf_mem_keys {r : Registry N K V E} {k : K} {m : N}
    (h : providerOf r k = some m) : m ∈ r.map (fun p => p.1) := by
  induction r with
  | nil => simp [providerOf] at h
  | cons p rest ih =>
      cases hlc : p.2.lc with
      | inactive _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩
      | loading _ _ _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩
      | active _ _ =>
          simp [providerOf, hlc] at h
          by_cases htbl : (p.2.table k).isSome
          · simp [htbl] at h
            rw [List.mem_map]
            exact ⟨p, by simp [h]⟩
          · simp [htbl] at h
            have hm := ih h
            rw [List.mem_map] at hm
            rcases hm with ⟨x, hx, hfst⟩
            rw [List.mem_map]
            exact ⟨x, by simp [hx], hfst⟩
      | unloading _ _ _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩

/-- A provider is an active fiber present in the registry. -/
theorem providerOf_some_lookup_active {r : Registry N K V E} {k : K} {m : N}
    (hn : NodupKeys r) (h : providerOf r k = some m) :
    ∃ g : Fiber N K V E, lookup r m = some g ∧ ∃ κ v, g.lc = .active κ v := by
  induction r with
  | nil => simp [providerOf] at h
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        exact hn.2
      cases hlc : p.2.lc with
      | inactive _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg
      | loading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg
      | active κ v =>
          simp [providerOf, hlc] at h
          by_cases htbl : (p.2.table k).isSome
          · simp [htbl] at h
            have hpm : p.1 = m := h
            refine ⟨p.2, by simp [lookup, hpm], κ, v, ?_⟩
            exact hlc
          · simp [htbl] at h
            rcases ih hnrest h with ⟨g, hg, hgact⟩
            have hpm : p.1 ≠ m := by
              intro hEq
              have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
              change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
              rw [List.nodup_cons] at hn
              exact hn.1 (by simpa [hEq] using hm)
            refine ⟨g, ?_, hgact⟩
            simpa [lookup, hpm] using hg
      | unloading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg

/-- If `targetOf r n = some v`, then `v` is the provider map on the
component's specification. -/
theorem targetOf_view_eq {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hl : lookup r n = some f) (ht : targetOf r n = some v) :
    ∀ k ∈ f.comp.spec, v k = providerOf r k := by
  intro k hk
  unfold targetOf at ht
  rw [hl] at ht
  change ((if f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec then none
    else some (fun k => if k ∈ f.comp.spec then providerOf r k else none)) = some v) at ht
  by_cases hc : f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec
  · rw [if_pos hc] at ht
    simp at ht
  · rw [if_neg hc] at ht
    have hv : v = fun k => if k ∈ f.comp.spec then providerOf r k else none :=
      (Option.some.inj ht).symm
    rw [hv]
    simp [hk]

/-- The target view of a fiber is total on its specification and names
installed fibers (well-formedness clauses (3)–(4) at `L-Begin`). -/
theorem targetOf_view_installed {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hn : NodupKeys r) (hl : lookup r n = some f)
    (ht : targetOf r n = some v) :
    (∀ k ∈ f.comp.spec, v k = providerOf r k)
      ∧ (∀ k ∈ f.comp.spec, ∃ m, v k = some m ∧ ∃ g, lookup r m = some g)
      ∧ (∀ k ∈ f.comp.spec, ∀ m, v k = some m →
          ∃ g, lookup r m = some g ∧ g.lc.installed) := by
  have hsat : satisfies (sigmaOf r) f.comp.spec := by
    rcases satisfies_of_target ht with ⟨g, hg, _, hsat⟩
    have hfg : f = g := Option.some.inj (hl.symm.trans hg)
    rw [hfg]
    exact hsat
  refine ⟨targetOf_view_eq hl ht, ?_, ?_⟩
  · intro k hk
    rw [targetOf_view_eq hl ht k hk]
    have hsome : (sigmaOf r k).isSome := hsat k hk
    have hprov : (providerOf r k).isSome := providerOf_isSome_of_sigmaOf_isSome hsome
    rcases Option.isSome_iff_exists.mp hprov with ⟨m, hm⟩
    rcases providerOf_some_lookup_active hn hm with ⟨g, hg, hgact⟩
    exact ⟨m, hm, g, hg⟩
  · intro k hk m hvm
    rw [targetOf_view_eq hl ht k hk] at hvm
    rcases providerOf_some_lookup_active hn hvm with ⟨g, hg, κ, vg, hlc⟩
    exact ⟨g, hg, by rw [hlc]; trivial⟩

/-! ## Well-formedness (Definition 58) -/

/-- **Definition 58, clauses (1)–(2).** The shape invariant of a registry:
parent pointers land in the registry, and the provisions of distinct fibers
are disjoint.  (Clauses (3)–(4) are in `WellFormed` below.) -/
structure WellFormedBase (r : Registry N K V E) : Prop where
  parentOk : ∀ n f, lookup r n = some f → ∀ m ∈ f.parent,
    ∃ f', lookup r m = some f'
  provDisj : ∀ n f n' f', lookup r n = some f → lookup r n' = some f' →
    n ≠ n' → ∀ k ∈ f.comp.prov, ∀ k' ∈ f'.comp.prov, k ≠ k'

/-- **Definition 58.** A registry is well formed when its names are
duplicate-free, (1) parent pointers land, (2) provisions of distinct fibers
are disjoint, (3) an installed fiber's committed view is total on its
specification and names registered fibers, and (4) a committed view names
only installed fibers. -/
structure WellFormed (r : Registry N K V E) : Prop where
  nodupKeys : NodupKeys r
  parentOk : ∀ n f, lookup r n = some f → ∀ m ∈ f.parent,
    ∃ f', lookup r m = some f'
  provDisj : ∀ n f n' f', lookup r n = some f → lookup r n' = some f' →
    n ≠ n' → ∀ k ∈ f.comp.prov, ∀ k' ∈ f'.comp.prov, k ≠ k'
  viewTotal : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k ∈ f.comp.spec, ∃ m, f.lc.viewOf k = some m ∧ ∃ g, lookup r m = some g
  viewInstalled : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k ∈ f.comp.spec, ∀ m, f.lc.viewOf k = some m →
    ∃ g, lookup r m = some g ∧ g.lc.installed

/-- Project `WellFormed` to its first two clauses. -/
theorem WellFormed.toBase {r : Registry N K V E} (hwf : WellFormed r) : WellFormedBase r :=
  ⟨hwf.parentOk, hwf.provDisj⟩

/-! ## Preservation of clauses (1)–(2) under all ten rules -/

/-- Pointwise update at an existing name preserves `WellFormedBase` when
the component and the parent are unchanged. -/
theorem wellFormedBase_set (hwf : WellFormedBase r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hp : old.parent = new.parent) : WellFormedBase (set r n new) := by
  constructor
  · intro m g hm x hx
    obtain ⟨g₂, hg₂⟩ : ∃ g₂, lookup r x = some g₂ := by
      rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact hwf.parentOk n old h x (hp.symm ▸ (hg ▸ hx))
      · exact hwf.parentOk m g hg x hx
    by_cases hxn : x = n
    · subst hxn
      exact ⟨new, lookup_set_eq r _ new⟩
    · rw [lookup_set_ne r n x new hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    have toR : ∀ a α (ha : lookup (set r n new) a = some α),
        ∃ β, lookup r a = some β ∧ β.comp = α.comp := by
      intro a α ha
      rcases lookup_set_cases ha with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · subst heq; subst hg
        exact ⟨old, h, hc⟩
      · exact ⟨α, hg, rfl⟩
    obtain ⟨β, hb, hβ⟩ := toR m g hm
    obtain ⟨β', hb', hβ'⟩ := toR m' g' hm'
    have hk₁ : k ∈ β.comp.prov := by rw [hβ]; exact hk
    have hk₂ : k' ∈ β'.comp.prov := by rw [hβ']; exact hk'
    exact hwf.provDisj m β m' β' hb hb' hne k hk₁ k' hk₂

/-- Pointwise update at a fresh name preserves `WellFormedBase`. -/
theorem wellFormedBase_setFresh (hwf : WellFormedBase r) {n : N} {c : Component K V E}
    {p : Option N} {fresh : Fiber N K V E}
    (hnone : lookup r n = none) (hcomp : fresh.comp = c)
    (hpar : fresh.parent = p) (hp : ∀ x ∈ p, ∃ g, lookup r x = some g)
    (hdisj : ∀ m g, lookup r m = some g →
      ∀ k ∈ c.prov, ∀ k' ∈ g.comp.prov, k ≠ k') :
    WellFormedBase (set r n fresh) := by
  constructor
  · intro m g hm x hx
    have hgr : lookup r m = some g ∨ (m = n ∧ g = fresh) := by
      rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact .inr ⟨heq, hg⟩
      · exact .inl hg
    have hland : ∃ g₂, lookup r x = some g₂ := by
      rcases hgr with hg | ⟨heq, hg⟩
      · exact hwf.parentOk m g hg x hx
      · subst heq; subst hg
        rw [hpar] at hx
        exact hp x hx
    obtain ⟨g₂, hg₂⟩ := hland
    by_cases hxn : x = n
    · subst hxn
      exact ⟨fresh, lookup_set_eq r _ fresh⟩
    · rw [lookup_set_ne r n x fresh hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    by_cases hmn : m = n
    · rw [hmn, lookup_set_eq] at hm
      have hgf : g = fresh := (Option.some.inj hm).symm
      rw [hgf, hcomp] at hk
      have hg' : lookup r m' = some g' := by
        rcases lookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd (hmn.trans heq.symm) hne
        · exact hg
      exact hdisj m' g' hg' k hk k' hk'
    · have hmOld : lookup r m = some g := by
        rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd heq hmn
        · exact hg
      by_cases hmn' : m' = n
      · rw [hmn', lookup_set_eq] at hm'
        have hgf : g' = fresh := (Option.some.inj hm').symm
        rw [hgf, hcomp] at hk'
        exact fun heq => hdisj m g hmOld k' hk' k hk heq.symm
      · have hmOld' : lookup r m' = some g' := by
          rcases lookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
          · exact absurd heq hmn'
          · exact hg
        exact hwf.provDisj m g m' g' hmOld hmOld' hne k hk k' hk'

/-- Removal preserves `WellFormedBase` when no fiber points at the removed
name. -/
theorem wellFormedBase_del (hwf : WellFormedBase r) {n : N}
    (hchild : ∀ m g, lookup r m = some g → g.parent ≠ some n) :
    WellFormedBase (del r n) := by
  constructor
  · intro m g hm x hx
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hne, hg⟩
    obtain ⟨g₂, hg₂⟩ := hwf.parentOk m g hg x hx
    have hxn : x ≠ n := by
      intro heq; subst heq
      simp only [Option.mem_def] at hx
      exact hchild m g hg hx
    rw [lookup_del_ne r n x hxn]
    exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨_, hg⟩
    have hc' := lookup_del_cases (n := n) hm'
    rcases hc' with ⟨_, hg'⟩
    exact hwf.provDisj m g m' g' hg hg' hne k hk k' hk'

/-- **Theorem 59 (Preservation), clauses (1)–(2), full calculus.**  If `r`
is well formed then so is the registry any of the ten rules reaches. -/
theorem wellFormedBase_preserved {r r' : Registry N K V E} (hwf : WellFormedBase r)
    (h : Ostep r r' ∨ Lstep r r') : WellFormedBase r' := by
  rcases h with h | h
  · cases h with
    | oInsert n c p hn hp hdisj => exact wellFormedBase_setFresh hwf hn rfl rfl hp hdisj
    | oRetire n f hf => exact wellFormedBase_set hwf hf rfl rfl
    | oRemove n f o hf hl hchild => exact wellFormedBase_del hwf hchild
  · cases h with
    | lBegin n f v hf hl ht => exact wellFormedBase_set hwf hf rfl rfl
    | lIter n f ι κ v ι' δ h hf hl ht hstep => exact wellFormedBase_set hwf hf rfl rfl
    | lFinish n f ι κ v δ h hf hl ht hstep => exact wellFormedBase_set hwf hf rfl rfl
    | lRaise n f ι κ v e hf hl hstep => exact wellFormedBase_set hwf hf rfl rfl
    | lDivertAbort n f ι κ v hf hl ht => exact wellFormedBase_set hwf hf rfl rfl
    | lDivertLand n f ι κ v δ h c hf hl ht hstep => exact wellFormedBase_set hwf hf rfl rfl
    | lLeave n f κ v hf hl ht => exact wellFormedBase_set hwf hf rfl rfl
    | lUnload n f κ v o hf hl hg => exact wellFormedBase_set hwf hf rfl rfl

/-! ## Full preservation (Theorem 59, all clauses) -/

/-- A pointwise update at an existing name preserves full well-formedness
when the update keeps the component, the parent, and the committed view, and
does not newly install the fiber. -/
theorem wellFormed_set_viewSame (hwf : WellFormed r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hp : old.parent = new.parent)
    (hinst : new.lc.installed → old.lc.installed)
    (hinst' : old.lc.installed → new.lc.installed)
    (hview : ∀ k, new.lc.viewOf k = old.lc.viewOf k) :
    WellFormed (set r n new) := by
  have hb := wellFormedBase_set hwf.toBase h hc hp
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hk_old : k ∈ old.comp.spec := by simpa [hc] using hk
      have hold : old.lc.installed := hinst hinst_m
      rcases hwf.viewTotal n old h hold k hk_old with ⟨p, hv, hlp⟩
      refine ⟨p, ?_, ?_⟩
      · rw [hview k]; exact hv
      · by_cases hpn : p = n
        · subst p; exact ⟨new, lookup_set_eq r n new⟩
        · rw [lookup_set_ne r n p new hpn]; exact hlp
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hk_old : k ∈ old.comp.spec := by simpa [hc] using hk
      have hold : old.lc.installed := hinst hinst_m
      have hv_old : old.lc.viewOf k = some p := by
        rw [hview k] at hvm
        exact hvm
      rcases hwf.viewInstalled n old h hold k hk_old p hv_old with ⟨q, hq, hqinst⟩
      by_cases hpn : p = n
      · subst p
        exact ⟨new, lookup_set_eq r n new, hinst_m⟩
      · rw [lookup_set_ne r n p new hpn]
        exact ⟨q, hq, hqinst⟩
    · rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      by_cases hpn : p = n
      · subst p
        have hqold : q = old := Option.some.inj (hq.symm.trans h)
        have hold_n : old.lc.installed := by simpa [hqold] using hqinst
        exact ⟨new, lookup_set_eq r n new, hinst' hold_n⟩
      · rw [lookup_set_ne r n p new hpn]
        exact ⟨q, hq, hqinst⟩

/-- `O-Insert` preserves full well-formedness. -/
theorem wellFormed_setFreshFull (hwf : WellFormed r) {n : N} {c : Component K V E}
    {p : Option N} {fresh : Fiber N K V E}
    (hnone : lookup r n = none) (hcomp : fresh.comp = c)
    (hpar : fresh.parent = p) (hp : ∀ x ∈ p, ∃ g, lookup r x = some g)
    (hdisj : ∀ m g, lookup r m = some g →
      ∀ k ∈ c.prov, ∀ k' ∈ g.comp.prov, k ≠ k')
    (hfresh : fresh.lc = .inactive none) :
    WellFormed (set r n fresh) := by
  have hb := wellFormedBase_setFresh hwf.toBase hnone hcomp hpar hp hdisj
  constructor
  · exact nodupKeys_set r n fresh hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      rw [hfresh] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨fresh, lookup_set_eq r n fresh⟩
      · rw [lookup_set_ne r n p fresh hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      rw [hfresh] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      have hpn : p ≠ n := by
        intro heq; subst p
        rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨q', hq', hq'inst⟩
        rw [hnone] at hq'
        simp at hq'
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p fresh hpn]
      exact hq

/-- `O-Remove` preserves full well-formedness. -/
theorem wellFormed_delFull (hwf : WellFormed r) {n : N} {f : Fiber N K V E}
    {o : Option E} (h : lookup r n = some f) (hl : f.lc = .inactive o)
    (hchild : ∀ m g, lookup r m = some g → g.parent ≠ some n) :
    WellFormed (del r n) := by
  have hb := wellFormedBase_del hwf.toBase hchild
  constructor
  · exact nodupKeys_del r n hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hmn, hg⟩
    rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
    refine ⟨p, hv, ?_⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      rcases hwf.viewInstalled m g hg hinst_m k hk n hv with ⟨gn, hgn, hgninst⟩
      have hgn_f : gn = f := Option.some.inj (hgn.symm.trans h)
      rw [hgn_f, hl] at hgninst
      unfold Lifecycle.installed at hgninst
      cases hgninst
    rw [lookup_del_ne r n p hpn]
    exact hlp
  · intro m g hm hinst_m k hk p hvm
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hmn, hg⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨gn, hgn, hgninst⟩
      have hgn_f : gn = f := Option.some.inj (hgn.symm.trans h)
      rw [hgn_f, hl] at hgninst
      unfold Lifecycle.installed at hgninst
      cases hgninst
    rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
    refine ⟨q, ?_, hqinst⟩
    rw [lookup_del_ne r n p hpn]
    exact hq

/-- `L-Begin` preserves full well-formedness: the target view is total on
the specification and names installed fibers. -/
theorem wellFormed_lBegin (hwf : WellFormed r) {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hf : lookup r n = some f) (hl : f.lc = .inactive none)
    (ht : targetOf r n = some v) :
    WellFormed (set r n { f with lc := .loading f.comp.iter id v }) := by
  let new : Fiber N K V E := { f with lc := .loading f.comp.iter id v }
  have hb : WellFormedBase (set r n new) :=
    wellFormedBase_set (old := f) (new := new) hwf.toBase hf rfl rfl
  have htn := targetOf_view_installed hwf.nodupKeys hf ht
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hkf : k ∈ f.comp.spec := by simpa using hk
      rcases htn.2.1 k hkf with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hkf : k ∈ f.comp.spec := by simpa using hk
      change v k = some p at hvm
      have hvmv : v k = some p := hvm
      have hpn : p ≠ n := by
        intro heq; subst p
        rcases htn.2.2 k hkf n hvmv with ⟨q, hq, hqinst⟩
        have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
        rw [hq_f, hl] at hqinst
        unfold Lifecycle.installed at hqinst
        cases hqinst
      rcases htn.2.2 k hkf p hvmv with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq
    · have hpn : p ≠ n := by
        intro heq; subst p
        rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨q, hq, hqinst⟩
        have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
        rw [hq_f, hl] at hqinst
        unfold Lifecycle.installed at hqinst
        cases hqinst
      rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq

/-- `L-Unload` preserves full well-formedness: the guard `¬ relied` keeps
other committed views from naming the now-inactive fiber. -/
theorem wellFormed_lUnload (hwf : WellFormed r) {n : N} {f : Fiber N K V E}
    {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N} {o : Option E}
    (hf : lookup r n = some f) (_hl : f.lc = .unloading κ v o)
    (hg : ¬ relied r n) :
    WellFormed (set r n { f with lc := .inactive o }) := by
  let new : Fiber N K V E := { f with lc := .inactive o }
  have hb : WellFormedBase (set r n new) :=
    wellFormedBase_set (old := f) (new := new) hwf.toBase hf rfl rfl
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
    · subst m; subst g
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewTotal m g hg' hinst_m k hk with ⟨p, hv, hlp⟩
      have hpn : p ≠ n := by
        intro heq; subst p
        exact hg ⟨m, k, g, hg', hmn, hinst_m, by simpa using hv⟩
      refine ⟨p, hv, ?_⟩
      rw [lookup_set_ne r n p new hpn]
      exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
    · subst m; subst g
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · have hpn : p ≠ n := by
        intro heq; subst p
        exact hg ⟨m, k, g, hg', hmn, hinst_m, by simpa using hvm⟩
      rcases hwf.viewInstalled m g hg' hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq

/-- **Theorem 59 (Preservation), full calculus.**  If `r` is well formed
then so is the registry any of the ten rules reaches. -/
theorem WellFormed.preserved {r r' : Registry N K V E} (hwf : WellFormed r)
    (h : Ostep r r' ∨ Lstep r r') : WellFormed r' := by
  rcases h with h | h
  · cases h with
    | oInsert n c p hn hp hdisj =>
        exact wellFormed_setFreshFull hwf hn rfl rfl hp hdisj rfl
    | oRetire n f hf =>
        let new : Fiber N K V E := { f with retired := true }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro h; exact h) (by intro h; exact h)
          (by intro k; rfl)
    | oRemove n f o hf hl hchild =>
        exact wellFormed_delFull hwf hf hl hchild
  · cases h with
    | lBegin n f v hf hl ht =>
        exact wellFormed_lBegin hwf hf hl ht
    | lIter n f ι κ v ι' δ hinv hf hl ht hstep =>
        let new : Fiber N K V E := { f with lc := .loading ι' (κ ∘ hinv) v }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lFinish n f ι κ v δ hinv hf hl ht hstep =>
        let new : Fiber N K V E := { f with lc := .active (κ ∘ hinv) v }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lRaise n f ι κ v e hf hl hstep =>
        let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lDivertAbort n f ι κ v hf hl ht =>
        let new : Fiber N K V E := { f with lc := .unloading κ v none }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lDivertLand n f ι κ v δ hinv c hf hl ht hstep =>
        let new : Fiber N K V E := { f with lc := .unloading (κ ∘ hinv) v none }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lLeave n f κ v hf hl ht =>
        let new : Fiber N K V E := { f with lc := .unloading κ v none }
        exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
    | lUnload n f κ v o hf hl hg =>
        exact wellFormed_lUnload hwf hf hl hg

/-! ## Precedence and acyclicity (Definition 65) -/

/-- **Definition 65.** `n` precedes `m` when `n` may provide a key that `m`
declares: `P_n ∩ S_m ≠ ∅`. -/
def Precedes (r : Registry N K V E) (n m : N) : Prop :=
  ∃ f g, lookup r n = some f ∧ lookup r m = some g ∧
    ∃ k, k ∈ f.comp.prov ∧ k ∈ g.comp.spec

/-- Acyclicity of precedence, phrased as well-foundedness of the inverse
relation (no infinite increasing chains). -/
def Acyclic (r : Registry N K V E) : Prop :=
  WellFounded (fun n m => Precedes r m n)

/-! ## Progress: no deadlock except the guarded unload -/



/-- **Theorem 66, clause 1 (full calculus).** A non-quiescent state either
admits a lifecycle step, or has a fiber in `unloading` whose guard
(`relied`) is still closed.  With the acyclicity hypothesis of the paper the
second case is impossible; here we make the disjunction explicit. -/
theorem exists_lstep_or_guarded {r : Registry N K V E} (h : ¬ quiet r) :
    (∃ r', Lstep r r') ∨
    (∃ n f κ v o, lookup r n = some f ∧ f.lc = .unloading κ v o ∧ relied r n) := by
  have hex : ∃ n f, lookup r n = some f ∧ ¬ (match f.lc with
    | .inactive o => o ≠ none ∨ targetOf r n = none
    | .loading _ _ _ => False
    | .active _ v => targetOf r n = some v
    | .unloading _ _ _ => False) := by
    refine Classical.byContradiction fun hc => h ?_
    intro n f hl
    by_cases hh : (match f.lc with
      | .inactive o => o ≠ none ∨ targetOf r n = none
      | .loading _ _ _ => False
      | .active _ v => targetOf r n = some v
      | .unloading _ _ _ => False)
    · exact hh
    · exact absurd ⟨n, f, hl, hh⟩ hc
  obtain ⟨n, f, hf, hnot⟩ := hex
  cases hlc : f.lc with
  | inactive o =>
      rw [hlc] at hnot
      by_cases ho : o = none
      · subst o
        simp at hnot
        cases ht : targetOf r n with
        | none => exact absurd ht hnot
        | some v => exact .inl ⟨_, Lstep.lBegin r n f v hf hlc ht⟩
      · have ho' : o ≠ none := ho
        exact absurd (Or.inl ho') hnot
  | loading ι κ v =>
      rw [hlc] at hnot
      by_cases ht : targetOf r n = some v
      · cases hstep : Iterator.step ι (sigmaOf r) with
        | error e => exact .inl ⟨_, Lstep.lRaise r n f ι κ v e hf hlc hstep⟩
        | ok res =>
            rcases res with ⟨δ, h, c⟩
            cases c with
            | none => exact .inl ⟨_, Lstep.lFinish r n f ι κ v δ h hf hlc ht hstep⟩
            | some ι' => exact .inl ⟨_, Lstep.lIter r n f ι κ v ι' δ h hf hlc ht hstep⟩
      · exact .inl ⟨_, Lstep.lDivertAbort r n f ι κ v hf hlc ht⟩
  | active κ v =>
      rw [hlc] at hnot
      exact .inl ⟨_, Lstep.lLeave r n f κ v hf hlc hnot⟩
  | unloading κ v o =>
      rw [hlc] at hnot
      by_cases hg : relied r n
      · exact .inr ⟨n, f, κ, v, o, hf, hlc, hg⟩
      · exact .inl ⟨_, Lstep.lUnload r n f κ v o hf hlc hg⟩


/-! ## Full progress under acyclicity and view-provider invariants -/

/-- A loading fiber always has a lifecycle step. -/
theorem exists_lstep_of_loading {r : Registry N K V E} {m : N} {g : Fiber N K V E}
    {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} (hg : lookup r m = some g) (hlc : g.lc = .loading ι κ v) :
    ∃ r', Lstep r r' := by
  by_cases ht : targetOf r m = some v
  · cases hstep : Iterator.step ι (sigmaOf r) with
    | error e => exact ⟨_, Lstep.lRaise r m g ι κ v e hg hlc hstep⟩
    | ok res =>
        rcases res with ⟨δ, h, c⟩
        cases c with
        | none => exact ⟨_, Lstep.lFinish r m g ι κ v δ h hg hlc ht hstep⟩
        | some ι' => exact ⟨_, Lstep.lIter r m g ι κ v ι' δ h hg hlc ht hstep⟩
  · exact ⟨_, Lstep.lDivertAbort r m g ι κ v hg hlc ht⟩

/-- An active fiber whose target equals its committed view cannot have a
committed view naming a fiber that is unloading: the provider of the key
would have to be both active and unloading. -/
theorem active_view_unload_false {r : Registry N K V E} (hwf : WellFormed r)
    (hviewSpec : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec)
    {m : N} {g : Fiber N K V E} {κg : CoefCtx K V → CoefCtx K V}
    {vg : K → Option N} {k : K} {n : N}
    (hg : lookup r m = some g) (hlc : g.lc = .active κg vg)
    (ht : targetOf r m = some vg) (hvm : g.lc.viewOf k = some n)
    {f : Fiber N K V E} (hlook_n : lookup r n = some f)
    (hlc_n : f.lc = .unloading κ v o) : False := by
  have hvm' : vg k = some n := by
    rw [hlc] at hvm
    simpa [Lifecycle.viewOf] using hvm
  have hk_spec : k ∈ g.comp.spec := hviewSpec m g hg (by rw [hlc]; trivial) k (by
    intro hnone
    have hnone' : vg k = none := by
      rw [hlc] at hnone
      simpa [Lifecycle.viewOf] using hnone
    rw [hnone'] at hvm'
    simp at hvm')
  have htv : vg k = providerOf r k := targetOf_view_eq hg ht k hk_spec
  have hprov : providerOf r k = some n := by
    rw [htv] at hvm'
    exact hvm'
  rcases providerOf_some_lookup_active hwf.nodupKeys hprov with ⟨gn, hgn, κn, vn, hlc_gn⟩
  have hgn_f : gn = f := Option.some.inj (hgn.symm.trans hlook_n)
  rw [hgn_f] at hlc_gn
  rw [hlc_gn] at hlc_n
  cases hlc_n

/-- From a guarded unloading fiber, another guarded unloading fiber is
reached, and precedence strictly increases. -/
theorem next_guarded_of_guarded {r : Registry N K V E} (hwf : WellFormed r)
    (hviewSpec : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec)
    (hviewProv : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k m, f.lc.viewOf k = some m →
      ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov)
    (hno : ¬ ∃ r', Lstep r r')
    {n : N} {f : Fiber N K V E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {o : Option E}
    (hlook_n : lookup r n = some f) (hlc_n : f.lc = .unloading κ v o)
    (hrel : relied r n) :
    ∃ m g κ' v' o', lookup r m = some g ∧ g.lc = .unloading κ' v' o'
      ∧ relied r m ∧ Precedes r n m := by
  rcases hrel with ⟨m, k, g, hg, hmn, hinst_m, hv_mk⟩
  have hk_spec : k ∈ g.comp.spec :=
    hviewSpec m g hg hinst_m k (by
      intro hnone
      rw [hnone] at hv_mk
      simp at hv_mk)
  cases hlc_m : g.lc with
  | inactive _ =>
      exfalso
      rw [hlc_m] at hinst_m
      cases hinst_m
  | loading _ _ _ =>
      exfalso
      exact hno (exists_lstep_of_loading hg hlc_m)
  | active κg vg =>
      by_cases ht : targetOf r m = some vg
      · exfalso
        exact active_view_unload_false hwf hviewSpec hg hlc_m ht hv_mk hlook_n hlc_n
      · exfalso
        exact hno ⟨_, Lstep.lLeave r m g κg vg hg hlc_m ht⟩
  | unloading κg vg og =>
      by_cases hrel_m : relied r m
      · refine ⟨m, g, κg, vg, og, hg, hlc_m, hrel_m, ?_⟩
        rcases hviewProv m g hg hinst_m k n hv_mk with ⟨gn, hgn, hk_prov⟩
        have hgn_f : gn = f := Option.some.inj (hgn.symm.trans hlook_n)
        have hk_prov_f : k ∈ f.comp.prov := by
          rw [hgn_f] at hk_prov
          exact hk_prov
        exact ⟨f, g, hlook_n, hg, k, hk_prov_f, hk_spec⟩
      · exfalso
        exact hno ⟨_, Lstep.lUnload r m g κg vg og hg hlc_m hrel_m⟩

/-- Under acyclicity, the guarded-unload disjunct is impossible. -/
theorem no_guarded_unload_of_acyclic {r : Registry N K V E} (hwf : WellFormed r) (hacyc : Acyclic r)
    (hviewSpec : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec)
    (hviewProv : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k m, f.lc.viewOf k = some m →
      ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov)
    (hno : ¬ ∃ r', Lstep r r') :
    ∀ n f κ v o, lookup r n = some f → f.lc = .unloading κ v o → ¬ relied r n := by
  intro n
  refine @WellFounded.induction N (fun a b : N => Precedes r b a) hacyc
    (fun n => ∀ f κ v o, lookup r n = some f → f.lc = .unloading κ v o → ¬ relied r n) n ?_
  intro x ih f κ v o hlook_n hlc_n hrel
  rcases next_guarded_of_guarded hwf hviewSpec hviewProv hno hlook_n hlc_n hrel
    with ⟨m, g, κ', v', o', hg, hlc_m, hrel_m, hprec⟩
  have hprecR : (fun a b => Precedes r b a) m x := hprec
  have hC_m := ih m hprecR g κ' v' o' hg hlc_m
  exact hC_m hrel_m

/-- **Theorem 66, clause 1 (full calculus), conditional on the two
view-provider invariants that confinement (Definition 48) supplies.**  A
non-quiescent, well-formed, acyclic state admits a lifecycle step. -/
theorem exists_lstep_of_not_quiet_of_acyclic {r : Registry N K V E} (hwf : WellFormed r) (hacyc : Acyclic r)
    (hviewSpec : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec)
    (hviewProv : ∀ n f, lookup r n = some f → f.lc.installed →
      ∀ k m, f.lc.viewOf k = some m →
      ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov)
    (h : ¬ quiet r) : ∃ r', Lstep r r' := by
  apply Classical.byContradiction
  intro hno
  rcases exists_lstep_or_guarded h with hstep | hguard
  · exact hno hstep
  · rcases hguard with ⟨n, f, κ, v, o, hf, hl, hr⟩
    exact (no_guarded_unload_of_acyclic hwf hacyc hviewSpec hviewProv hno n f κ v o hf hl) hr

/-! ## Confinement-derived invariant and final progress statement -/

/-- The invariants that the confinement discipline of Definition 48
supplies for a registry: installed committed views only name declared keys,
installed committed views name only fibers whose provision contains that
key, and every table key is in the fiber's provision.  These are exactly
what the acyclic progress theorem needs. -/
structure ConfinedWellFormed (r : Registry N K V E) : Prop where
  wf : WellFormed r
  viewSpec : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec
  tableProv : ∀ n f, lookup r n = some f →
    ∀ k, (f.table k).isSome → k ∈ f.comp.prov
  viewProv : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k m, f.lc.viewOf k = some m →
    ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov

/-- **Theorem 66, clause 1 (full calculus).**  Under acyclic precedence
and the confinement-derived invariants, a non-quiescent registry admits a
lifecycle step. -/
theorem exists_lstep_of_not_quiet {r : Registry N K V E} (hwf : ConfinedWellFormed r)
    (hacyc : Acyclic r) (h : ¬ quiet r) : ∃ r', Lstep r r' :=
  exists_lstep_of_not_quiet_of_acyclic hwf.wf hacyc hwf.viewSpec hwf.viewProv h

/-! ## Quiescence and the absence of lifecycle steps -/

/-- **Quiescence is sound.**  In a quiescent state no lifecycle rule
applies. -/
theorem no_lstep_of_quiet {r : Registry N K V E} (hq : quiet r) :
    ¬ ∃ r', Lstep r r' := by
  rintro ⟨r', hstep⟩
  cases hstep with
  | lBegin n f v hf hl ht =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
      rw [hq'] at ht
      simp at ht
  | lIter n f ι κ v ι' δ h hf hl ht hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lFinish n f ι κ v δ h hf hl ht hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lRaise n f ι κ v e hf hl hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lDivertAbort n f ι κ v hf hl ht =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lDivertLand n f ι κ v δ h c hf hl ht hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lLeave n f κ v hf hl ht =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
      exact ht hq'
  | lUnload n f κ v o hf hl hg =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'

end Full

end Cordix
