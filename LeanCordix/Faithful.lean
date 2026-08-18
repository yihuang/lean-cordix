import LeanCordix.FullCtx
import LeanCordix.Iterator
import LeanCordix.Coeffect
import LeanCordix.TraceModel
import LeanCordix.Independence

/-!
# Cordix — Faithful full-context model (parallel development)

This module is the faithful counterpart of `FullCalculus` / `TraceModel`:
iterators run against the full context `FullCtx = (ambient, sigma)` rather
than against `sigmaOf` alone.  It is intentionally developed in parallel so
the existing model stays green while the faithful definitions and theorems
are built out.

Current contents:

* `Faithful.Component` — component with `Iterator (FullCtx K V) E`;
* `Faithful.Lifecycle` — lifecycle carrying `FullCtx → FullCtx` accumulators;
* `Faithful.Fiber`, `Faithful.Registry`, `Faithful.State`;
* the derived context operations `sigmaOf`, `providerOf`, `targetOf`,
  `quiet`, `relied`, and `State.fullCtx`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Faithful

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- The faithful iterator context: `(ambient, sigma)`. -/
abbrev Ctx (K : Type) (V : K → Type u) : Type _ :=
  Full.FullCtx K V

/-- **Faithful Definition 43.** A component whose effect iterator runs on the
full context. -/
structure Component (K : Type) (V : K → Type u) (E : Type) where
  /-- The dependencies required from the environment. -/
  spec : Spec K
  /-- The keys the component may provide. -/
  prov : List K
  /-- The effect iterator executed on activation. -/
  iter : Iterator (Ctx K V) E
  /-- The iterator is witnessed, including all reachable continuations. -/
  wit : Iterator.WitnessedAll iter

/-- **Faithful Definition 48 (writes half).** An iterator is confined to a
provision `P` when every successful step leaves the sigma component
unchanged outside `P`.  This is the map-level write bound used to show that
recomputed effects are still confined after recovery. -/
def ConfinedIterator {K : Type} {V : K → Type u} {E : Type}
    (ι : Iterator (Ctx K V) E) (P : List K) : Prop :=
  ∀ γ : Ctx K V, match Iterator.step ι γ with
    | .ok (δ, _, _) => ∀ k, k ∉ P → γ.2 k = δ.2 k
    | .error _ => True

/-- **Faithful Definition 48 (writes half) for accumulators.** An
accumulator is confined to `P` when it leaves the sigma component unchanged
outside `P`. -/
def ConfinedAcc {K : Type} {V : K → Type u}
    (κ : Ctx K V → Ctx K V) (P : List K) : Prop :=
  ∀ γ : Ctx K V, ∀ k, k ∉ P → γ.2 k = (κ γ).2 k

/-- A component is confined when every reachable iterator is
write-confined to its provision.  The accumulator half is stated as a
separate global assumption in the trace theorems, since accumulators are
stored in lifecycle records. -/
def Component.Confined (c : Component K V E) : Prop :=
  ∀ {ι' : Iterator (Ctx K V) E}, Iterator.Reachable c.iter ι' →
    ConfinedIterator ι' c.prov

/-- **Faithful Definition 49.** Lifecycle states with full-context
accumulators. -/
inductive Lifecycle (N : Type) (K : Type) (V : K → Type u) (E : Type)
  | inactive (outcome : Option E) : Lifecycle N K V E
  | loading (iter : Iterator (Ctx K V) E) (acc : Ctx K V → Ctx K V)
      (view : K → Option N) : Lifecycle N K V E
  | active (acc : Ctx K V → Ctx K V) (view : K → Option N) :
      Lifecycle N K V E
  | unloading (acc : Ctx K V → Ctx K V) (view : K → Option N)
      (outcome : Option E) : Lifecycle N K V E

namespace Lifecycle

/-- A fiber is installed when it is not inactive. -/
def installed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive _ => False
  | .loading _ _ _ => True
  | .active _ _ => True
  | .unloading _ _ _ => True

/-- The committed view of a lifecycle state. -/
def viewOf {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → K → Option N
  | .inactive _ => fun _ => none
  | .loading _ _ v => v
  | .active _ v => v
  | .unloading _ v _ => v

/-- A fiber is failed when it has reached an error outcome. -/
def failed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive (some _) => True
  | _ => False

/-- The accumulator carried by a lifecycle state; `id` for inactive. -/
def acc {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Ctx K V → Ctx K V
  | .inactive _ => id
  | .loading _ κ _ => κ
  | .active κ _ => κ
  | .unloading κ _ _ => κ

/-- A lifecycle is write-confined to a provision when its iterator (if any)
and its accumulator are both confined. -/
def Confined {N K : Type} {V : K → Type u} {E : Type}
    (lc : Lifecycle N K V E) (P : List K) : Prop :=
  match lc with
  | .inactive _ => True
  | .loading ι κ _ => ConfinedIterator ι P ∧ ConfinedAcc κ P
  | .active κ _ => ConfinedAcc κ P
  | .unloading κ _ _ => ConfinedAcc κ P

end Lifecycle

/-- **Faithful Definition 44.** A fiber in the faithful model. -/
structure Fiber (N : Type) (K : Type) (V : K → Type u) (E : Type) where
  comp : Component K V E
  parent : Option N
  table : CoefCtx K V
  retired : Bool
  lc : Lifecycle N K V E

/-- **Faithful Definition 45.** The registry: a list of named fibers. -/
abbrev Registry (N K : Type) (V : K → Type u) (E : Type) :=
  List (N × Fiber N K V E)

/-- Lookup in a registry. -/
def lookup {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Option (Fiber N K V E)
  | [], _ => none
  | p :: rest, n => if p.1 = n then some p.2 else lookup rest n

/-- Pointwise update. -/
def set {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Fiber N K V E → Registry N K V E
  | [], n, f => [(n, f)]
  | p :: rest, n, f =>
      if p.1 = n then (n, f) :: rest else p :: set rest n f

/-- Lookup after a pointwise update at the same name. -/
theorem lookup_set_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (n : N) (f : Fiber N K V E) :
    lookup (set r n f) n = some f := by
  induction r with
  | nil => simp [set, lookup]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · simp [set, lookup, h]
      · simp [set, lookup, h, ih]

/-- Lookup after a pointwise update at a different name. -/
theorem lookup_set_ne {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (n m : N) (f : Fiber N K V E) (hne : m ≠ n) :
    lookup (set r n f) m = lookup r m := by
  induction r with
  | nil => simp [set, lookup, Ne.symm hne]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · simp [set, lookup, h, Ne.symm hne]
      · by_cases hm : p.1 = m
        · simp [set, lookup, h, hm, hne]
        · simp [set, lookup, h, hm, ih]

/-- Removal. -/
def del {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Registry N K V E
  | [], _ => []
  | p :: rest, n => if p.1 = n then del rest n else p :: del rest n

/-- If a name is not in a registry's keys, lookup returns `none`. -/
theorem lookup_none_of_not_mem {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    (h : n ∉ r.map (fun p => p.1)) : lookup r n = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        apply h
        simp [hEq]
      have hrest : n ∉ rest.map (fun p => p.1) := by
        intro hn
        apply h
        simp [hn]
      simp [lookup, hpn, ih hrest]

/-- Deleting a name removes that name from lookups. -/
theorem lookup_del_self {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N} :
    lookup (del r n) n = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases h : p.1 = n
      · rw [show del (p :: rest) n = del rest n by simp [del, h]]
        exact ih
      · rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        simp [lookup, h, ih]

/-- Deleting a different name does not change lookups. -/
theorem lookup_del_ne {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n m : N}
    (hne : m ≠ n) : lookup (del r n) m = lookup r m := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases h : p.1 = n
      · rw [show del (p :: rest) n = del rest n by simp [del, h]]
        have hpm : p.1 ≠ m := by
          intro hEq
          apply hne
          rw [← h, hEq]
        simp [lookup, hpm, ih]
      · rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        by_cases hm : p.1 = m
        · simp [lookup, hm]
        · simp [lookup, hm, ih]

/-- Updating the same name twice keeps the second update. -/
theorem set_set_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (n : N) (f g : Fiber N K V E) :
    set (set r n f) n g = set r n g := by
  induction r with
  | nil => simp [set]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · simp [set, h]
      · simp [set, h, ih]

/-- Replacing the first occurrence of a name by the fiber already found
there is the identity on registries. -/
theorem set_eq_self_of_lookup_eq {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {f : Fiber N K V E} (hf : lookup r n = some f) : set r n f = r := by
  induction r with
  | nil => cases hf
  | cons p rest ih =>
      by_cases h : p.1 = n
      · have hp : p.2 = f := by
          simpa [lookup, h] using hf
        simp [set, h]
        exact Prod.ext h.symm hp.symm
      · simp [set, h]
        exact ih (by simpa [lookup, h] using hf)

/-- The names of a registry are duplicate-free. -/
def NodupKeys {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) : Prop :=
  List.Nodup (r.map (fun p => p.1))

/-- Distinct fibers have disjoint tables: at any key, at most one fiber has a
value.  This is the table-level reading of well-formedness clause (2) once
every fiber's writes are confined to its own provision. -/
def PairwiseDisjointTables {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) : Prop :=
  ∀ p ∈ r, ∀ q ∈ r, p.1 ≠ q.1 →
    ∀ k, p.2.table k = none ∨ q.2.table k = none

/-- In a duplicate-free registry, lookups at the same name return the same
fiber. -/
theorem lookup_eq_of_nodup {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} (hnodup : NodupKeys r)
    {n : N} {f g : Fiber N K V E} (hf : lookup r n = some f)
    (hg : lookup r n = some g) : f = g := by
  induction r with
  | nil => cases hf
  | cons p rest ih =>
      by_cases h : p.1 = n
      · have hf' : p.2 = f := by simpa [lookup, h] using hf
        have hg' : p.2 = g := by simpa [lookup, h] using hg
        exact hf'.symm.trans hg'
      · have hf_rest : lookup rest n = some f := by simpa [lookup, h] using hf
        have hg_rest : lookup rest n = some g := by simpa [lookup, h] using hg
        have hnodup_rest : NodupKeys rest := by
          have hn : List.Nodup (p.1 :: rest.map (fun q => q.1)) := by
            simpa [NodupKeys] using hnodup
          exact (List.nodup_cons.mp hn).2
        exact ih hnodup_rest hf_rest hg_rest

/-- `lookup` records membership of the pair it found. -/
theorem lookup_some_mem {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    (h : lookup r n = some f) : (n, f) ∈ r := by
  induction r with
  | nil => cases h
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rw [lookup, if_pos hp] at h
        have hpf : p.2 = f := Option.some.inj h
        cases p with
        | mk n' g =>
            simp at hp hpf ⊢
            subst n'
            subst f
            simp
      · rw [lookup, if_neg hp] at h
        exact List.mem_cons_of_mem p (ih h)

/-- In a duplicate-free registry, membership determines the lookup. -/
theorem lookup_self_of_mem_of_nodup {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} (hn : NodupKeys r)
    {p : N × Fiber N K V E} (hp : p ∈ r) : lookup r p.1 = some p.2 := by
  induction r with
  | nil => cases hp
  | cons q rest ih =>
      simp at hp
      rcases hp with hpq | hrest
      · subst q
        simp [lookup]
      · have hnrest : NodupKeys rest := by
          have hn' : List.Nodup (q.1 :: rest.map (fun x => x.1)) := by
            simpa [NodupKeys] using hn
          exact (List.nodup_cons.mp hn').2
        have hlook := ih hnrest hrest
        have hne : p.1 ≠ q.1 := by
          intro hEq
          have hmem : p.1 ∈ rest.map (fun x => x.1) := by
            exact List.mem_map_of_mem (f := fun x : N × Fiber N K V E => x.1) hrest
          have hnodup_cons : List.Nodup (q.1 :: rest.map (fun x => x.1)) := by
            simpa [NodupKeys] using hn
          exact (List.nodup_cons.mp hnodup_cons).1 (hEq ▸ hmem)
        simp [lookup, Ne.symm hne, hlook]

/-- Membership in `del r n` implies membership in `r`. -/
theorem mem_of_mem_del {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E}
    {q : N × Fiber N K V E} {n : N} (h : q ∈ del r n) : q ∈ r := by
  induction r with
  | nil => cases h
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · simp [del, hpn] at h
        exact List.mem_cons_of_mem p (ih h)
      · simp [del, hpn] at h
        rcases h with hpq | hrest
        · simp [hpq]
        · exact List.mem_cons_of_mem p (ih hrest)

/-- If a name is in the map of `del r n`, it is in the map of `r`. -/
theorem mem_map_del {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {a : N} {n : N} :
    a ∈ (del r n).map (fun p => p.1) → a ∈ r.map (fun p => p.1) := by
  intro hm
  rcases List.mem_map.mp hm with ⟨q, hq, rfl⟩
  exact List.mem_map.mpr ⟨q, mem_of_mem_del hq, rfl⟩

/-- Deleting a name preserves pairwise disjointness of tables. -/
theorem pairwiseDisjointTables_del {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} (hdisj : PairwiseDisjointTables r)
    (n : N) : PairwiseDisjointTables (del r n) := by
  intro a ha b hb hab k
  exact hdisj a (mem_of_mem_del ha) b (mem_of_mem_del hb) hab k

/-- The pointwise update does not add old keys under new names. -/
theorem key_not_mem_set {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N} {f : Fiber N K V E} {p : N}
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

/-- The pointwise update preserves duplicate-free names. -/
theorem nodupKeys_set {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (r : Registry N K V E) (n : N) (f : Fiber N K V E)
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

/-- If a pair with a key different from `n` is in `set r n f`, it is already
in `r` (the pointwise update only changes the entry at `n`). -/
theorem mem_of_mem_set_ne {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {p : N × Fiber N K V E} (hp : p ∈ set r n f) (hpn : p.1 ≠ n) : p ∈ r := by
  revert hpn
  induction r with
  | nil =>
      intro hpn
      simp [set] at hp
      subst hp
      exact False.elim (hpn rfl)
  | cons q rest ih =>
      intro hpn
      by_cases hq : q.1 = n
      · subst n
        simp [set] at hp
        rcases hp with hpq | hrest
        · have hp_eq : p.1 = q.1 := by rw [hpq]
          exact False.elim (hpn (by simpa [hp_eq]))
        · exact List.mem_cons_of_mem q hrest
      · simp [set, hq] at hp
        rcases hp with hpq | hrest
        · subst q
          simp
        · exact List.mem_cons_of_mem q (ih hrest hpn)

/-- Replacing or inserting a fiber with a table that is disjoint from all
other existing tables preserves pairwise disjointness. -/
theorem pairwiseDisjointTables_set_of_table_disjoint_from_others {N : Type}
    [DecidableEq N] {K : Type} [DecidableEq K] {V : K → Type u} {E : Type}
    {r : Registry N K V E} (hnodup : NodupKeys r) (hdisj : PairwiseDisjointTables r)
    {n : N} {g : Fiber N K V E}
    (hdisj_new : ∀ p ∈ r, p.1 ≠ n → ∀ k, g.table k ≠ none → p.2.table k = none) :
    PairwiseDisjointTables (set r n g) := by
  intro a ha b hb hab k
  have hnodup' : NodupKeys (set r n g) := nodupKeys_set r n g hnodup
  rcases a with ⟨aN, aF⟩
  rcases b with ⟨bN, bF⟩
  have ha_lookup : lookup (set r n g) aN = some aF := by
    simpa using lookup_self_of_mem_of_nodup hnodup' ha
  have hb_lookup : lookup (set r n g) bN = some bF := by
    simpa using lookup_self_of_mem_of_nodup hnodup' hb
  by_cases han : aN = n
  · subst aN
    have hg_a : aF = g := by
      exact lookup_eq_of_nodup hnodup' ha_lookup (lookup_set_eq r n g)
    by_cases hbn : bN = n
    · subst bN
      exact False.elim (hab rfl)
    · have hb_mem : (bN, bF) ∈ r := mem_of_mem_set_ne hb hbn
      by_cases hg_none : g.table k = none
      · subst aF
        exact Or.inl hg_none
      · have hb_none : bF.table k = none := hdisj_new (bN, bF) hb_mem hbn k hg_none
        subst aF
        exact Or.inr hb_none
  · have ha_mem : (aN, aF) ∈ r := mem_of_mem_set_ne ha han
    by_cases hbn : bN = n
    · subst bN
      have hg_b : bF = g := by
        exact lookup_eq_of_nodup hnodup' hb_lookup (lookup_set_eq r n g)
      by_cases hg_none : g.table k = none
      · subst bF
        exact Or.inr hg_none
      · have ha_none : aF.table k = none := hdisj_new (aN, aF) ha_mem han k hg_none
        subst bF
        exact Or.inl ha_none
    · have hb_mem : (bN, bF) ∈ r := mem_of_mem_set_ne hb hbn
      exact hdisj (aN, aF) ha_mem (bN, bF) hb_mem (by
        intro hEq
        exact hab hEq) k

/-- Replacing or inserting a fiber with an empty table preserves pairwise
disjointness. -/
theorem pairwiseDisjointTables_set_empty {N : Type} [DecidableEq N]
    {K : Type} [DecidableEq K] {V : K → Type u} {E : Type} {r : Registry N K V E}
    (hnodup : NodupKeys r) (hdisj : PairwiseDisjointTables r)
    {n : N} {g : Fiber N K V E} (hg : g.table = fun _ => none) :
    PairwiseDisjointTables (set r n g) := by
  intro a ha b hb hab k
  have hnodup' : NodupKeys (set r n g) := nodupKeys_set r n g hnodup
  rcases a with ⟨aN, aF⟩
  rcases b with ⟨bN, bF⟩
  have ha_lookup : lookup (set r n g) aN = some aF := by
    simpa using lookup_self_of_mem_of_nodup hnodup' ha
  have hb_lookup : lookup (set r n g) bN = some bF := by
    simpa using lookup_self_of_mem_of_nodup hnodup' hb
  by_cases han : aN = n
  · subst aN
    have hg_a : aF = g := by
      exact lookup_eq_of_nodup hnodup' ha_lookup (lookup_set_eq r n g)
    subst aF
    simp [hg]
  · have ha_mem : (aN, aF) ∈ r := mem_of_mem_set_ne ha han
    by_cases hbn : bN = n
    · subst bN
      have hg_b : bF = g := by
        exact lookup_eq_of_nodup hnodup' hb_lookup (lookup_set_eq r n g)
      subst bF
      simp [hg]
    · have hb_mem : (bN, bF) ∈ r := mem_of_mem_set_ne hb hbn
      exact hdisj (aN, aF) ha_mem (bN, bF) hb_mem (by
        intro hEq
        exact hab hEq) k

/-- Replacing a fiber while keeping its table preserves pairwise
disjointness. -/
theorem pairwiseDisjointTables_set_preserves_table {N : Type} [DecidableEq N]
    {K : Type} [DecidableEq K] {V : K → Type u} {E : Type} {r : Registry N K V E}
    (hnodup : NodupKeys r) (hdisj : PairwiseDisjointTables r)
    {n : N} {g new : Fiber N K V E} (hg : lookup r n = some g)
    (htable : new.table = g.table) : PairwiseDisjointTables (set r n new) := by
  apply pairwiseDisjointTables_set_of_table_disjoint_from_others hnodup hdisj
  intro p hp hpn k hk
  have hg_nonne : g.table k ≠ none := by
    rw [← htable]
    exact hk
  rcases hdisj (n, g) (lookup_some_mem hg) p hp (by
    intro hEq
    exact hpn hEq.symm) k with hg_none | hp_none
  · exact False.elim (hg_nonne hg_none)
  · exact hp_none

/-- If a name does not occur in a registry, deleting it is the identity. -/
theorem del_eq_self_of_not_mem {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    (h : n ∉ r.map (fun p => p.1)) : del r n = r := by
  induction r with
  | nil => simp [del]
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        apply h
        simp [hEq]
      have hrest : n ∉ rest.map (fun p => p.1) := by
        intro hn
        apply h
        simp [hn]
      simp [del, hpn, ih hrest]

/-- `del` preserves duplicate-freeness. -/
theorem nodupKeys_del {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} (hn : NodupKeys r) (n : N) :
    NodupKeys (del r n) := by
  induction r with
  | nil => simp [NodupKeys, del]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · have hnrest : NodupKeys rest := by
          have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
            simpa [NodupKeys] using hn
          exact (List.nodup_cons.mp hn').2
        simpa [del, h] using ih hnrest
      · have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        have hnrest : NodupKeys rest := (List.nodup_cons.mp hn').2
        have hpn : p.1 ∉ rest.map (fun x => x.1) := (List.nodup_cons.mp hn').1
        have ih' := ih hnrest
        have hmem : p.1 ∉ (del rest n).map (fun x => x.1) := by
          intro hm
          exact hpn (mem_map_del hm)
        rw [NodupKeys, del, if_neg h]
        change List.Nodup (p.1 :: (del rest n).map (fun x => x.1))
        rw [NodupKeys] at ih'
        exact List.nodup_cons.mpr ⟨hmem, ih'⟩

/-- The coeffect context of a state: the union of the tables of active
fibers. -/
def sigmaOf {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => p.2.table k <|> acc
    | _ => acc

/-- The **raw** coeffect context of a registry: the union of every fiber's
table, regardless of lifecycle.  This is the table content of the paper's
full context `Γ∞`; the active-only `sigmaOf` remains the context read by the
rules. -/
def rawSigma {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc => p.2.table k <|> acc

/-- **Confinement split.**  Given the full new sigma produced by an effect
confined to a fiber with provision `prov`, the fiber's own table is the
restriction of that sigma to `prov`; outside `prov` the sigma is owned by
other fibers. -/
def splitTable {K : Type} [DecidableEq K] {V : K → Type u}
    (prov : List K) (σ : CoefCtx K V) : CoefCtx K V :=
  fun k => if k ∈ prov then σ k else none

/-- The provider of a key: the active fiber whose table defines it. -/
def providerOf {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (k : K) : Option N :=
  r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => if (p.2.table k).isSome then some p.1 else acc
    | _ => acc

/-- The target view of `n` at `r`. -/
noncomputable def targetOf {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (r : Registry N K V E) (n : N) : Option (K → Option N) :=
  match lookup r n with
  | some f =>
      if f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec then none
      else some (fun k => if k ∈ f.comp.spec then providerOf r k else none)
  | none => none

/-- Quiescence in the faithful model. -/
def quiet {N : Type} [DecidableEq N] {K : Type} [DecidableEq K] {V : K → Type u}
    {E : Type} (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f →
    match f.lc with
    | .inactive o => o ≠ none ∨ targetOf r n = none
    | .loading _ _ _ => False
    | .active _ v => targetOf r n = some v
    | .unloading _ _ _ => False

/-- The withdrawal guard. -/
def relied {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (n : N) : Prop :=
  ∃ n' k f, lookup r n' = some f ∧ n' ≠ n ∧ f.lc.installed
    ∧ f.lc.viewOf k = some n

/-- **Faithful state.** The registry together with the ambient remainder. -/
structure State (N : Type) (K : Type) (E : Type) (V : K → Type u) where
  reg : Registry N K V E
  ambient : CoefCtx K V

namespace State

/-- The full context of a faithful state: ambient paired with the raw union
of every fiber's table (matching the paper's `Γ∞`, not the active-only
`Σ_γ`). -/
def fullCtx {N : Type} {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) : Ctx K V :=
  (s.ambient, Faithful.rawSigma s.reg)

/-- The coeffect context of a faithful state. -/
def sigmaOf {N : Type} {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) : CoefCtx K V :=
  Faithful.sigmaOf s.reg

/-- The provider map of a faithful state. -/
def providerOf {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (k : K) : Option N :=
  Faithful.providerOf s.reg k

/-- The target view of `n` at a faithful state. -/
noncomputable def targetOf {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} (s : State N K E V) (n : N) : Option (K → Option N) :=
  Faithful.targetOf s.reg n

/-- Quiescence at a faithful state. -/
def quiet {N : Type} [DecidableEq N] {K : Type} [DecidableEq K] {E : Type}
    {V : K → Type u} (s : State N K E V) : Prop :=
  Faithful.quiet s.reg

/-- The withdrawal guard at a faithful state. -/
def relied {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (n : N) : Prop :=
  Faithful.relied s.reg n

/-- The full-context accumulator carried by a fiber at a state; `id` when the
fiber is absent. -/
def accAt {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) : Ctx K V → Ctx K V :=
  match lookup s.reg n with
  | some f => Lifecycle.acc f.lc
  | none => id

/-- `accAt` reads the lifecycle accumulator of the fiber found in the
registry. -/
theorem accAt_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    {s : State N K E V} {n : N} {f : Fiber N K V E}
    (hf : lookup s.reg n = some f) :
    State.accAt s n = Lifecycle.acc f.lc := by
  simp [State.accAt, hf]

/-- **Faithful full recovery** `κ_n(s)`.  Apply the fiber's accumulator to
the full context `(ambient, sigma)`; the recovered ambient is the first
component, and the fiber's own table is emptied (its contribution has been
withdrawn from the context).  This is the state-level reading of the paper's
`κ_n` that makes Eq. (56) meaningful when the tracked fiber has written its
own table. -/
def recover (s : State N K E V) (n : N) : State N K E V :=
  match lookup s.reg n with
  | some f =>
      match f.lc with
      | .inactive _ => s
      | .loading _ κ _ =>
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩
      | .active κ _ =>
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩
      | .unloading κ _ _ =>
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩
  | none => s

/-- If a freshly begun fiber has an empty table and the identity accumulator,
full recovery is the identity. -/
theorem recover_of_loading_id {s : State N K E V} {n : N}
    {f : Fiber N K V E} {v : K → Option N}
    (hf : lookup s.reg n = some f) (htable : f.table = fun _ => none)
    (hl : f.lc = .loading f.comp.iter id v) :
    State.recover s n = s := by
  cases f with
  | mk comp parent table retired lc =>
      have htable' : table = fun _ => none := by simpa using htable
      have hl' : lc = .loading comp.iter id v := by simpa using hl
      have hf' : lookup s.reg n =
          some (Fiber.mk comp parent (fun _ => none) retired
            (Lifecycle.loading comp.iter id v)) := by
        simpa [htable', hl'] using hf
      simp [State.recover, hf, htable', hl', State.fullCtx,
        set_eq_self_of_lookup_eq hf']

/-- `recover` on a loading fiber applies its accumulator to the full context
and empties the fiber's table. -/
theorem recover_loading_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u}
    {E : Type} {s : State N K E V} {n : N} {f : Fiber N K V E}
    {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v) :
    State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
  simp [State.recover, hf, hl]

/-- `recover` on an active fiber applies its accumulator to the full context
and empties the fiber's table. -/
theorem recover_active_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u}
    {E : Type} {s : State N K E V} {n : N} {f : Fiber N K V E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v) :
    State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
  simp [State.recover, hf, hl]

/-- `recover` on an unloading fiber applies its accumulator to the full
context and empties the fiber's table. -/
theorem recover_unloading_eq {N : Type} [DecidableEq N] {K : Type} {V : K → Type u}
    {E : Type} {s : State N K E V} {n : N} {f : Fiber N K V E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N} {o : Option E}
    (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o) :
    State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
  simp [State.recover, hf, hl]

/-- The faithful withdrawal invariant: applying the accumulator at `n` to
`fullCtx s` already describes the full context after recovery.  This is the
model-level condition that makes Eq. (56) work when the tracked fiber has
written its own table. -/
def Withdraws {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) : Prop :=
  State.fullCtx (State.recover s n) = State.accAt s n (State.fullCtx s)

/-- The table half of withdrawal: the accumulator at `n` leaves the sigma
component unchanged on the provision list `P` of another fiber. -/
def WithdrawsOn {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (s : State N K E V) (n : N) (P : List K) : Prop :=
  match lookup s.reg n with
  | some f => ∀ γ, splitTable P ((Lifecycle.acc f.lc γ).2) = splitTable P γ.2
  | none => True

/-- Write a table at `n`, leaving the ambient unchanged. -/
def writeTable {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (δ : CoefCtx K V) : State N K E V :=
  match lookup s.reg n with
  | some g => ⟨set s.reg n { g with table := δ }, s.ambient⟩
  | none => s

/-- Write an effect at `n`: the sigma component becomes the fiber's table and
the ambient component becomes the new ambient. -/
def writeEffect {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (s : State N K E V) (n : N) (δ : Ctx K V) : State N K E V :=
  match lookup s.reg n with
  | some g => ⟨set s.reg n { g with table := splitTable g.comp.prov δ.2 }, δ.1⟩
  | none => s

/-- `writeEffect` at a present fiber unfolds to the explicit record. -/
theorem writeEffect_eq_of_lookup {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} {s : State N K E V} {m : N} {g : Fiber N K V E}
    (hg : lookup s.reg m = some g) (δ : Ctx K V) :
    State.writeEffect s m δ =
      ⟨set s.reg m { g with table := splitTable g.comp.prov δ.2 }, δ.1⟩ := by
  simp [State.writeEffect, hg]

/-- `recover` at `n` leaves the lookup at a different name unchanged. -/
theorem lookup_recover_ne {s : State N K E V} {n m : N}
    (hmn : n ≠ m) :
    lookup (State.recover s n).reg m = lookup s.reg m := by
  unfold State.recover
  by_cases hn : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp hn with ⟨f, hf⟩
    cases hlc : f.lc <;>
      simp [hf, hlc, lookup_set_ne, Ne.symm hmn]
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp hn
    simp [hn']

/-- `writeEffect` at `m` leaves the lookup at a different name unchanged. -/
theorem lookup_writeEffect_ne {s : State N K E V} {n m : N}
    (hmn : n ≠ m) {g : Fiber N K V E} (hg : lookup s.reg n = some g)
    (δ : Ctx K V) :
    lookup (State.writeEffect s m δ).reg n = some g := by
  unfold State.writeEffect
  by_cases hm : (lookup s.reg m).isSome
  · rcases Option.isSome_iff_exists.mp hm with ⟨h, hh⟩
    simp [hh, lookup_set_ne s.reg m n { h with table := splitTable h.comp.prov δ.2 } hmn, hg]
  · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
    simp [hm', hg]

/-- `writeEffect` at the same name updates that fiber's lookup. -/
theorem lookup_writeEffect_eq {s : State N K E V} {n : N} {f : Fiber N K V E}
    (hf : lookup s.reg n = some f) (δ : Ctx K V) :
    lookup (State.writeEffect s n δ).reg n =
      some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
  unfold State.writeEffect
  rw [hf]
  simp [lookup_set_eq]

/-- `writeEffect` preserves duplicate-free names. -/
theorem writeEffect_preserves_nodupKeys {s : State N K E V} {n : N} {δ : Ctx K V}
    (hn : NodupKeys s.reg) : NodupKeys (State.writeEffect s n δ).reg := by
  unfold State.writeEffect
  by_cases h : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h with ⟨g, hg⟩
    simp [hg]
    exact nodupKeys_set s.reg n { g with table := splitTable g.comp.prov δ.2 } hn
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp h
    simp [hn']
    exact hn

/-- `recover` preserves duplicate-free names. -/
theorem recover_preserves_nodupKeys {s : State N K E V} {n : N}
    (hn : NodupKeys s.reg) : NodupKeys (State.recover s n).reg := by
  unfold State.recover
  by_cases h : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h with ⟨f, hf⟩
    cases hlc : f.lc with
    | inactive o =>
        simp [hf, hlc]
        exact hn
    | loading i κ v =>
        simpa [hf, hlc] using nodupKeys_set s.reg n
          { f with table := fun _ => none, lc := Lifecycle.loading i κ v } hn
    | active κ v =>
        simpa [hf, hlc] using nodupKeys_set s.reg n
          { f with table := fun _ => none, lc := Lifecycle.active κ v } hn
    | unloading κ v o =>
        simpa [hf, hlc] using nodupKeys_set s.reg n
          { f with table := fun _ => none, lc := Lifecycle.unloading κ v o } hn
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp h
    simp [hn']
    exact hn

/-- `recover` preserves pairwise disjointness of tables. -/
theorem recover_preserves_pairwiseDisjointTables {s : State N K E V} {n : N}
    (hnodup : NodupKeys s.reg) (hdisj : PairwiseDisjointTables s.reg) :
    PairwiseDisjointTables (State.recover s n).reg := by
  unfold State.recover
  by_cases h : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h with ⟨f, hf⟩
    cases hlc : f.lc with
    | inactive o =>
        simp [hf, hlc]
        exact hdisj
    | loading i κ v =>
        simpa [hf, hlc] using pairwiseDisjointTables_set_empty hnodup hdisj
          (g := { f with table := fun _ => none, lc := Lifecycle.loading i κ v }) rfl
    | active κ v =>
        simpa [hf, hlc] using pairwiseDisjointTables_set_empty hnodup hdisj
          (g := { f with table := fun _ => none, lc := Lifecycle.active κ v }) rfl
    | unloading κ v o =>
        simpa [hf, hlc] using pairwiseDisjointTables_set_empty hnodup hdisj
          (g := { f with table := fun _ => none, lc := Lifecycle.unloading κ v o }) rfl
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp h
    simp [hn']
    exact hdisj

end State

/-- A `FullCtx` delta is **confined to `n`** when, outside `n`'s provision,
the new sigma agrees with the old raw sigma (other fibers' tables are
unchanged), and the ambient component is arbitrary (the effect may write the
ambient). -/
def ConfinedEffect {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (s : State N K E V) (n : N)
    (δ : Ctx K V) : Prop :=
  ∃ f, lookup s.reg n = some f ∧
    (∀ k, k ∉ f.comp.prov → rawSigma s.reg k = δ.2 k) ∧
    (∀ k, k ∉ f.comp.prov → f.table k = none) ∧
    (∀ p ∈ s.reg, p.1 ≠ n →
      ∀ k ∈ f.comp.prov, p.2.table k = none)

/-- If an iterator is write-confined to a fiber's provision, any successful
step on a state produces a `ConfinedEffect` for that state (given the usual
table support/disjointness side conditions). -/
theorem confinedEffect_of_confinedIterator {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {δ : Ctx K V}
    (hf : lookup s.reg n = some f)
    (hι : ConfinedIterator ι f.comp.prov)
    (hstep : ∃ h c, Iterator.step ι (State.fullCtx s) = .ok (δ, h, c))
    (hsupport : ∀ k, k ∉ f.comp.prov → f.table k = none)
    (hdisj : ∀ p ∈ s.reg, p.1 ≠ n → ∀ k ∈ f.comp.prov, p.2.table k = none) :
    ConfinedEffect s n δ := by
  rcases hstep with ⟨h, c, hstep⟩
  refine ⟨f, hf, ?_, hsupport, hdisj⟩
  intro k hk
  have hout := hι (State.fullCtx s)
  rw [hstep] at hout
  exact hout k hk

/-- If an accumulator is write-confined to a fiber's provision, applying it
to the state's full context produces a `ConfinedEffect` for that state. -/
theorem confinedEffect_of_confinedAcc {s : State N K E V} {n : N}
    {f : Fiber N K V E} {κ : Ctx K V → Ctx K V}
    (hf : lookup s.reg n = some f)
    (hκ : ConfinedAcc κ f.comp.prov)
    (hsupport : ∀ k, k ∉ f.comp.prov → f.table k = none)
    (hdisj : ∀ p ∈ s.reg, p.1 ≠ n → ∀ k ∈ f.comp.prov, p.2.table k = none) :
    ConfinedEffect s n (κ (State.fullCtx s)) := by
  refine ⟨f, hf, ?_, hsupport, hdisj⟩
  intro k hk
  exact hκ (State.fullCtx s) k hk

/-- Recovery at `n` preserves the disjointness condition of a confined
effect at a different fiber `m`. -/
theorem recover_preserves_confined_disjoint {s : State N K E V} {m n : N}
    {f : Fiber N K V E} (hmn : m ≠ n) (hnodup : NodupKeys s.reg)
    (hf : lookup s.reg m = some f)
    (hdisj : ∀ p ∈ s.reg, p.1 ≠ m → ∀ k ∈ f.comp.prov, p.2.table k = none) :
    ∀ p ∈ (State.recover s n).reg, p.1 ≠ m →
      ∀ k ∈ f.comp.prov, p.2.table k = none := by
  intro p hp hpm k hk
  unfold State.recover at hp
  by_cases hn : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp hn with ⟨g, hg⟩
    cases hlc : g.lc with
    | inactive o =>
        simp [State.recover, hg, hlc] at hp
        exact hdisj p hp hpm k hk
    | loading i κ v =>
        simp [State.recover, hg, hlc] at hp
        rcases p with ⟨a, h⟩
        by_cases ha : a = n
        · subst a
          have hset : lookup (set s.reg n { g with table := fun _ => none, lc := .loading i κ v }) n =
              some ({ g with table := fun _ => none, lc := .loading i κ v } : Fiber N K V E) :=
            lookup_set_eq s.reg n { g with table := fun _ => none, lc := .loading i κ v }
          have hset_nodup : NodupKeys (set s.reg n { g with table := fun _ => none, lc := .loading i κ v }) :=
            nodupKeys_set s.reg n { g with table := fun _ => none, lc := .loading i κ v } hnodup
          have hh : h = { g with table := fun _ => none, lc := .loading i κ v } :=
            lookup_eq_of_nodup hset_nodup (lookup_self_of_mem_of_nodup hset_nodup hp) hset
          subst h
          simp
        · have hp' : (a, h) ∈ s.reg := mem_of_mem_set_ne hp ha
          exact hdisj (a, h) hp' (by intro heq; exact hpm heq) k hk
    | active κ v =>
        simp [State.recover, hg, hlc] at hp
        rcases p with ⟨a, h⟩
        by_cases ha : a = n
        · subst a
          have hset : lookup (set s.reg n { g with table := fun _ => none, lc := .active κ v }) n =
              some ({ g with table := fun _ => none, lc := .active κ v } : Fiber N K V E) :=
            lookup_set_eq s.reg n { g with table := fun _ => none, lc := .active κ v }
          have hset_nodup : NodupKeys (set s.reg n { g with table := fun _ => none, lc := .active κ v }) :=
            nodupKeys_set s.reg n { g with table := fun _ => none, lc := .active κ v } hnodup
          have hh : h = { g with table := fun _ => none, lc := .active κ v } :=
            lookup_eq_of_nodup hset_nodup (lookup_self_of_mem_of_nodup hset_nodup hp) hset
          subst h
          simp
        · have hp' : (a, h) ∈ s.reg := mem_of_mem_set_ne hp ha
          exact hdisj (a, h) hp' (by intro heq; exact hpm heq) k hk
    | unloading κ v o =>
        simp [State.recover, hg, hlc] at hp
        rcases p with ⟨a, h⟩
        by_cases ha : a = n
        · subst a
          have hset : lookup (set s.reg n { g with table := fun _ => none, lc := .unloading κ v o }) n =
              some ({ g with table := fun _ => none, lc := .unloading κ v o } : Fiber N K V E) :=
            lookup_set_eq s.reg n { g with table := fun _ => none, lc := .unloading κ v o }
          have hset_nodup : NodupKeys (set s.reg n { g with table := fun _ => none, lc := .unloading κ v o }) :=
            nodupKeys_set s.reg n { g with table := fun _ => none, lc := .unloading κ v o } hnodup
          have hh : h = { g with table := fun _ => none, lc := .unloading κ v o } :=
            lookup_eq_of_nodup hset_nodup (lookup_self_of_mem_of_nodup hset_nodup hp) hset
          subst h
          simp
        · have hp' : (a, h) ∈ s.reg := mem_of_mem_set_ne hp ha
          exact hdisj (a, h) hp' (by intro heq; exact hpm heq) k hk
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp hn
    simp [State.recover, hn'] at hp
    exact hdisj p hp hpm k hk

/-- `writeEffect` preserves pairwise disjointness of tables under
confinement of the effect. -/
theorem State.writeEffect_preserves_pairwiseDisjointTables {s : State N K E V}
    {n : N} {δ : Ctx K V}
    (hnodup : NodupKeys s.reg) (hdisj : PairwiseDisjointTables s.reg)
    (hconf : ConfinedEffect s n δ) :
    PairwiseDisjointTables (State.writeEffect s n δ).reg := by
  by_cases h : (lookup s.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h with ⟨g, hg⟩
    rw [State.writeEffect_eq_of_lookup hg]
    apply pairwiseDisjointTables_set_of_table_disjoint_from_others hnodup hdisj
    intro p hp hpn k hk
    rcases hconf with ⟨f, hf, hout, hsupport, hdisj_prov⟩
    have hgf : g = f := lookup_eq_of_nodup hnodup hg hf
    subst g
    have hk_in : k ∈ f.comp.prov := by
      by_cases hkin : k ∈ f.comp.prov
      · exact hkin
      · exfalso
        simp [splitTable, hkin] at hk
    exact hdisj_prov p hp hpn k hk_in
  · have hn' : lookup s.reg n = none := Option.not_isSome_iff_eq_none.mp h
    simp [State.writeEffect, hn']
    exact hdisj

/-- `Option.or` is commutative when the two options are not both present. -/
theorem Option.or_comm_of_not_both {α : Type u} (a b : Option α)
    (h : a = none ∨ b = none) : (a <|> b) = (b <|> a) := by
  cases h with
  | inl ha => simp [ha]
  | inr hb => simp [hb]

/-- If every fiber's table is `none` at `k`, then the raw sigma is `none` at
`k`. -/
theorem rawSigma_eq_none_of_all_none {N : Type} {K : Type} {V : K → Type u} {E : Type}
    {r : Registry N K V E} {k : K}
    (h : ∀ p ∈ r, p.2.table k = none) : rawSigma r k = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      simp [rawSigma, h p (by simp)]
      exact (by simpa [rawSigma] using ih (fun q hq => h q (by simp [hq])))

/-- Replacing `n`'s table with `t` makes the raw sigma at `k` equal `t k`,
provided no other fiber defines `k`. -/
theorem rawSigma_set_table_eq_new {N : Type} [DecidableEq N] {K : Type} {V : K → Type u}
    {E : Type} {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    {t : CoefCtx K V} {k : K}
    (hnodup : NodupKeys r) (hg : lookup r n = some g)
    (hdisj : ∀ p ∈ r, p.1 ≠ n → p.2.table k = none) :
    rawSigma (set r n { g with table := t }) k = t k := by
  induction r with
  | nil => cases hg
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · have hp' : p.2 = g := by simpa [lookup, hp] using hg
        have hnodup_cons : List.Nodup (p.1 :: rest.map (fun q => q.1)) := by
          simpa [NodupKeys] using hnodup
        have hnmem : p.1 ∉ rest.map (fun q => q.1) :=
          (List.nodup_cons.mp hnodup_cons).1
        simp [set, hp, rawSigma]
        by_cases ht : t k = none
        · have hrest_none : rawSigma rest k = none := by
            apply rawSigma_eq_none_of_all_none
            intro q hq
            have hqne : q.1 ≠ n := by
              intro hqn
              apply hnmem
              rw [List.mem_map]
              exact ⟨q, hq, hqn.trans hp.symm⟩
            exact hdisj q (by simp [hq]) hqne
          simp [ht]
          simpa [rawSigma] using hrest_none
        · cases ht' : t k with
          | none => simp [ht'] at ht
          | some v => simp [ht']
      · have hnodup_rest : NodupKeys rest := by
          have hnodup_cons : List.Nodup (p.1 :: rest.map (fun q => q.1)) := by
            simpa [NodupKeys] using hnodup
          exact (List.nodup_cons.mp hnodup_cons).2
        have hg_rest : lookup rest n = some g := by
          simpa [lookup, hp] using hg
        have hdisj_rest : ∀ q ∈ rest, q.1 ≠ n → q.2.table k = none := by
          intro q hq hqn
          exact hdisj q (by simp [hq]) hqn
        have ih' := ih hnodup_rest hg_rest hdisj_rest
        have hp_table : p.2.table k = none := hdisj p (by simp) hp
        simp [set, hp, rawSigma, hp_table]
        simpa [rawSigma] using ih'

/-- Replacing `n`'s table with `t` does not change the raw sigma at `k` when
both the old and new tables are `none` at `k`. -/
theorem rawSigma_set_table_eq_old {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {g : Fiber N K V E} {t : CoefCtx K V} {k : K}
    (hnodup : NodupKeys r) (hg : lookup r n = some g)
    (ht : t k = none) (hold : g.table k = none) :
    rawSigma (set r n { g with table := t }) k = rawSigma r k := by
  induction r with
  | nil => cases hg
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · have hp' : p.2 = g := by simpa [lookup, hp] using hg
        simp [set, hp, rawSigma, ht, hold, hp']
      · have hnodup_rest : NodupKeys rest := by
          have hnodup_cons : List.Nodup (p.1 :: rest.map (fun q => q.1)) := by
            simpa [NodupKeys] using hnodup
          exact (List.nodup_cons.mp hnodup_cons).2
        have hg_rest : lookup rest n = some g := by
          simpa [lookup, hp] using hg
        have ih' := ih hnodup_rest hg_rest
        simp [set, hp, rawSigma]
        exact congrArg (fun x => (p.2.table k).or x) (by simpa [rawSigma] using ih')

/-- Changing only a fiber's lifecycle leaves the raw sigma unchanged. -/
theorem rawSigma_set_lc_eq {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {g : Fiber N K V E} {lc' : Lifecycle N K V E}
    (hf : lookup r n = some g) :
    rawSigma (set r n { g with lc := lc' }) = rawSigma r := by
  funext k
  induction r with
  | nil => cases hf
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · have hp' : p.2 = g := by simpa [lookup, hp] using hf
        simp [set, hp, rawSigma, hp']
      · have hg_rest : lookup rest n = some g := by
          simpa [lookup, hp] using hf
        have ih' := ih hg_rest
        simp [set, hp, rawSigma]
        exact congrArg (fun x => (p.2.table k).or x) (by simpa [rawSigma] using ih')

/-- Changing only a fiber's retired flag leaves the raw sigma unchanged. -/
theorem rawSigma_set_retired_eq {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {g : Fiber N K V E}
    (hf : lookup r n = some g) :
    rawSigma (set r n { g with retired := true }) = rawSigma r := by
  funext k
  induction r with
  | nil => cases hf
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · have hp' : p.2 = g := by simpa [lookup, hp] using hf
        simp [set, hp, rawSigma, hp']
      · have hg_rest : lookup rest n = some g := by
          simpa [lookup, hp] using hf
        have ih' := ih hg_rest
        simp [set, hp, rawSigma]
        exact congrArg (fun x => (p.2.table k).or x) (by simpa [rawSigma] using ih')

/-- Adding a fiber with an empty table at an absent name leaves the raw
sigma unchanged. -/
theorem rawSigma_set_empty_of_not_mem {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {g : Fiber N K V E} (hn : lookup r n = none) :
    rawSigma (set r n { g with table := fun _ => none }) = rawSigma r := by
  funext k
  induction r with
  | nil => simp [rawSigma, set]
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hp : lookup (p :: rest) n = some p.2 := by simp [lookup, hpn]
        rw [hn] at hp
        cases hp
      · have hnrest : lookup rest n = none := by
          simpa [lookup, hpn] using hn
        have ih' := ih hnrest
        simp [set, hpn, rawSigma]
        exact congrArg (fun x => (p.2.table k).or x) (by simpa [rawSigma] using ih')

/-- Adding a fresh inactive fiber with an empty table at an absent name
leaves the raw sigma unchanged. -/
theorem rawSigma_set_empty_fiber_of_not_mem {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {r : Registry N K V E} {n : N}
    {c : Component K V E} {p : Option N} (hn : lookup r n = none) :
    rawSigma (set r n (Fiber.mk c p (fun _ => none) false (.inactive none))) = rawSigma r := by
  funext k
  induction r with
  | nil => simp [rawSigma, set]
  | cons p₀ rest ih =>
      by_cases hpn : p₀.1 = n
      · have hp : lookup (p₀ :: rest) n = some p₀.2 := by simp [lookup, hpn]
        rw [hn] at hp
        cases hp
      · have hnrest : lookup rest n = none := by
          simpa [lookup, hpn] using hn
        have ih' := ih hnrest
        simp [set, hpn, rawSigma]
        exact congrArg (fun x => (p₀.2.table k).or x) (by simpa [rawSigma] using ih')

/-- Under confinement, writing an effect preserves the raw full-context
sigma. -/
theorem rawSigma_writeEffect_of_confined {s : State N K E V} {n : N} {δ : Ctx K V}
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    rawSigma (State.writeEffect s n δ).reg = δ.2 := by
  rcases hconf with ⟨f, hf, hout, hsupport, hdisj⟩
  funext k
  by_cases hk : k ∈ f.comp.prov
  · have hnew : rawSigma (State.writeEffect s n δ).reg k =
        splitTable f.comp.prov δ.2 k := by
      simp [State.writeEffect, hf]
      apply rawSigma_set_table_eq_new hnodup hf
      intro p hp pne
      exact hdisj p hp pne k hk
    have hsplit : splitTable f.comp.prov δ.2 k = δ.2 k := by
      simp [splitTable, hk]
    rw [hnew, hsplit]
  · have hnew : rawSigma (State.writeEffect s n δ).reg k = rawSigma s.reg k := by
      simp [State.writeEffect, hf]
      apply rawSigma_set_table_eq_old hnodup hf
      · simp [splitTable, hk]
      · exact hsupport k hk
    rw [hnew]
    exact hout k hk

/-- Under confinement, `writeEffect` makes the full context exactly the
effect's output `δ`. -/
theorem State.fullCtx_writeEffect_of_confined {s : State N K E V} {n : N}
    {δ : Ctx K V} (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.fullCtx (State.writeEffect s n δ) = δ := by
  unfold State.fullCtx
  have hconf' := hconf
  rcases hconf' with ⟨f, hf, _⟩
  simp [State.writeEffect, hf]
  apply Prod.ext
  · rfl
  · simpa [State.writeEffect, hf] using rawSigma_writeEffect_of_confined hnodup hconf

/-- Two confined writes with the same `δ` produce the same full context. -/
theorem State.writeEffect_preserves_fullCtx_of_confined {x y : State N K E V}
    {n : N} {δ : Ctx K V}
    (hnx : NodupKeys x.reg) (hny : NodupKeys y.reg)
    (hcx : ConfinedEffect x n δ) (hcy : ConfinedEffect y n δ) :
    State.fullCtx (State.writeEffect x n δ) = State.fullCtx (State.writeEffect y n δ) := by
  rw [State.fullCtx_writeEffect_of_confined hnx hcx,
      State.fullCtx_writeEffect_of_confined hny hcy]

/-- Fiber agreement at a single name, between two arbitrary states.  This is
the pointwise invariant that `PsiFiberAgrees` is built from. -/
def SameFiberAt {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (x y : State N K E V) (m : N) : Prop :=
  match lookup x.reg m, lookup y.reg m with
  | some gx, some gy => gx.comp.prov = gy.comp.prov
  | none, none => True
  | _, _ => False

/-- `SameFiberAt` is symmetric. -/
theorem sameFiberAt_comm {x y : State N K E V} {m : N} :
    SameFiberAt x y m ↔ SameFiberAt y x m := by
  unfold SameFiberAt
  cases hx : lookup x.reg m with
  | none =>
      cases hy : lookup y.reg m with
      | none => simp [hx, hy]
      | some gy => simp [hx, hy]
  | some gx =>
      cases hy : lookup y.reg m with
      | none => simp [hx, hy]
      | some gy => simp [hx, hy, eq_comm]

/-- `SameFiberAt` is transitive. -/
theorem sameFiberAt_trans {x y z : State N K E V} {m : N}
    (hxy : SameFiberAt x y m) (hyz : SameFiberAt y z m) : SameFiberAt x z m := by
  unfold SameFiberAt at *
  cases hx : lookup x.reg m with
  | none =>
      cases hy : lookup y.reg m with
      | none =>
          cases hz : lookup z.reg m with
          | none => simp [hx, hz]
          | some gz => simp [hx, hy, hz] at hyz
      | some gy => simp [hx, hy] at hxy
  | some gx =>
      cases hy : lookup y.reg m with
      | none => simp [hx, hy] at hxy
      | some gy =>
          cases hz : lookup z.reg m with
          | none => simp [hy, hz] at hyz
          | some gz =>
              simp [hx, hy, hz] at hxy hyz
              simp [hx, hz]
              exact hxy.trans hyz

/-- Pointwise `set` preserves fiber agreement: both sides receive the same
new fiber at `n`, and other names are untouched. -/
theorem set_preserves_sameFiberAt {x y : State N K E V} {n : N} {g : Fiber N K V E}
    {m : N} (h : SameFiberAt x y m) :
    SameFiberAt ⟨set x.reg n g, x.ambient⟩ ⟨set y.reg n g, y.ambient⟩ m := by
  by_cases hmn : m = n
  · subst m
    unfold SameFiberAt
    simp [lookup_set_eq]
  · unfold SameFiberAt
    rw [lookup_set_ne x.reg n m g hmn, lookup_set_ne y.reg n m g hmn]
    exact h

/-- Pointwise `set` with possibly different new fibers preserves fiber
agreement, provided the new fibers agree on their provision. -/
theorem set_preserves_sameFiberAt_of_prov {x y : State N K E V} {n : N}
    {gx gy : Fiber N K V E} {m : N} (h : SameFiberAt x y m)
    (hprov : gx.comp.prov = gy.comp.prov) :
    SameFiberAt ⟨set x.reg n gx, x.ambient⟩ ⟨set y.reg n gy, y.ambient⟩ m := by
  by_cases hmn : m = n
  · subst m
    unfold SameFiberAt
    simp [lookup_set_eq, hprov]
  · unfold SameFiberAt
    rw [lookup_set_ne x.reg n m gx hmn, lookup_set_ne y.reg n m gy hmn]
    exact h

/-- `writeEffect` preserves pointwise fiber agreement. -/
theorem State.writeEffect_preserves_sameFiberAt {x y : State N K E V} {n : N}
    {δx δy : Ctx K V} {m : N}
    (h : SameFiberAt x y m) :
    SameFiberAt (State.writeEffect x n δx) (State.writeEffect y n δy) m := by
  by_cases hmn : m = n
  · subst m
    unfold SameFiberAt
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := by
        unfold SameFiberAt at h
        rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
        rw [hgx] at h
        by_cases hy' : (lookup y.reg n).isSome
        · exact hy'
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
          simp [hyn] at h
      rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
      simp [State.writeEffect, hgx, hgy, lookup_set_eq]
      unfold SameFiberAt at h
      rw [hgx, hgy] at h
      exact h
    · have hy : ¬ (lookup y.reg n).isSome := by
        intro hy
        unfold SameFiberAt at h
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
        simp [hxn, hgy] at h
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [State.writeEffect, hxn, hyn]
  · have hx_lookup : lookup (State.writeEffect x n δx).reg m = lookup x.reg m := by
      unfold State.writeEffect
      by_cases hn : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hn with ⟨g, hg⟩
        simp [hg]
        exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δx.2 } hmn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hn
        simp [hn']
    have hy_lookup : lookup (State.writeEffect y n δy).reg m = lookup y.reg m := by
      unfold State.writeEffect
      by_cases hn : (lookup y.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hn with ⟨g, hg⟩
        simp [hg]
        exact lookup_set_ne y.reg n m { g with table := splitTable g.comp.prov δy.2 } hmn
      · have hn' : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hn
        simp [hn']
    unfold SameFiberAt
    rw [hx_lookup, hy_lookup]
    exact h

/-- `writeEffect` on the left preserves pointwise fiber agreement. -/
theorem State.writeEffect_preserves_sameFiberAt_left {x y : State N K E V} {n : N}
    {δ : Ctx K V} {m : N} (h : SameFiberAt x y m) :
    SameFiberAt (State.writeEffect x n δ) y m := by
  by_cases hmn : m = n
  · subst m
    unfold SameFiberAt
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := by
        unfold SameFiberAt at h
        rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
        rw [hgx] at h
        by_cases hy' : (lookup y.reg n).isSome
        · exact hy'
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
          simp [hyn] at h
      rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
      simp [State.writeEffect, hgx, hgy, lookup_set_eq]
      unfold SameFiberAt at h
      rw [hgx, hgy] at h
      exact h
    · have hy : ¬ (lookup y.reg n).isSome := by
        intro hy
        unfold SameFiberAt at h
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
        simp [hxn, hgy] at h
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [State.writeEffect, hxn, hyn]
  · have hx_lookup : lookup (State.writeEffect x n δ).reg m = lookup x.reg m := by
      unfold State.writeEffect
      by_cases hn : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hn with ⟨g, hg⟩
        simp [hg]
        exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ.2 } hmn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hn
        simp [hn']
    unfold SameFiberAt
    rw [hx_lookup]
    exact h

/-- `writeEffect` on the right preserves pointwise fiber agreement. -/
theorem State.writeEffect_preserves_sameFiberAt_right {x y : State N K E V} {n : N}
    {δ : Ctx K V} {m : N} (h : SameFiberAt x y m) :
    SameFiberAt x (State.writeEffect y n δ) m := by
  exact sameFiberAt_comm.mp (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δ) (m := m) (sameFiberAt_comm.mpr h))

/-! ## Faithful type-level step records -/

/-- The faithful analogue of `Full.Step`: a step record whose iterator runs
on `State.fullCtx` (ambient + sigma) and whose accumulator is a
`FullCtx → FullCtx` map. -/
inductive Step (s : State N K E V) : Type (max 1 u) where
  | oInsert (n : N) (c : Component K V E) (p : Option N)
      (hn : lookup s.reg n = none)
      (hp : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f)
      (hdisj : ∀ n' f, lookup s.reg n' = some f →
        (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
      Step s
  | oRetire (n : N) (f : Fiber N K V E)
      (hf : lookup s.reg n = some f) :
      Step s
  | oRemove (n : N) (f : Fiber N K V E) (o : Option E)
      (hf : lookup s.reg n = some f) (hl : f.lc = .inactive o)
      (hchild : ∀ n' f', lookup s.reg n' = some f' → f'.parent ≠ some n) :
      Step s
  | lBegin (n : N) (f : Fiber N K V E) (v : K → Option N)
      (hf : lookup s.reg n = some f) (hl : f.lc = .inactive none)
      (ht : targetOf s.reg n = some v)
      (htable : f.table = fun _ => none) :
      Step s
  | lIter (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (ι' : Iterator (Ctx K V) E)
      (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n = some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, some ι')) :
      Step s
  | lFinish (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n = some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, none)) :
      Step s
  | lRaise (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (e : E)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (hstep : Iterator.step ι (State.fullCtx s) = .error e) :
      Step s
  | lDivertAbort (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n ≠ some v) :
      Step s
  | lDivertLand (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (c : Option (Iterator (Ctx K V) E))
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n ≠ some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, c)) :
      Step s
  | lLeave (n : N) (f : Fiber N K V E)
      (κ : Ctx K V → Ctx K V) (v : K → Option N)
      (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v)
      (ht : targetOf s.reg n ≠ some v) :
      Step s
  | lUnload (n : N) (f : Fiber N K V E)
      (κ : Ctx K V → Ctx K V) (v : K → Option N) (o : Option E)
      (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o)
      (hg : ¬ relied s.reg n) :
      Step s

namespace Step

variable {s : State N K E V}

/-- The name the step acts on. -/
def name : Step s → N
  | oInsert n .. => n
  | oRetire n .. => n
  | oRemove n .. => n
  | lBegin n .. => n
  | lIter n .. => n
  | lFinish n .. => n
  | lRaise n .. => n
  | lDivertAbort n .. => n
  | lDivertLand n .. => n
  | lLeave n .. => n
  | lUnload n .. => n

/-- The rule kind of the step. -/
def kind : Step s → Full.StepKind
  | oInsert .. => Full.StepKind.oInsert
  | oRetire .. => Full.StepKind.oRetire
  | oRemove .. => Full.StepKind.oRemove
  | lBegin .. => Full.StepKind.lBegin
  | lIter .. => Full.StepKind.lIter
  | lFinish .. => Full.StepKind.lFinish
  | lRaise .. => Full.StepKind.lRaise
  | lDivertAbort .. => Full.StepKind.lDivertAbort
  | lDivertLand .. => Full.StepKind.lDivertLand
  | lLeave .. => Full.StepKind.lLeave
  | lUnload .. => Full.StepKind.lUnload

/-- The state map `Ψ`: writes the sigma component into the acting fiber's
table, the ambient component into the ambient context, applies the
accumulator at `L-Unload`, and is the identity elsewhere. -/
def psi : Step s → State N K E V → State N K E V
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lUnload n f κ v o hf hl hg, x =>
      match lookup x.reg n with
      | some g => State.writeEffect x n (κ (State.fullCtx x))
      | none => x
  | _, x => x

/-- The edit `edit`: writes only control fields, exactly as in the current
model but with full-context accumulators. -/
def edit : Step s → State N K E V → State N K E V
  | oInsert n c p hn hp hdisj, x =>
      ⟨set x.reg n ⟨c, p, fun _ => none, false, .inactive none⟩, x.ambient⟩
  | oRetire n f hf, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with retired := true }, x.ambient⟩
      | none => x
  | oRemove n f o hf hl hchild, x =>
      ⟨del x.reg n, x.ambient⟩
  | lBegin n f v hf hl ht htable, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .loading g.comp.iter id v }, x.ambient⟩
      | none => x
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .loading ι' (κ ∘ h) v }, x.ambient⟩
      | none => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .active (κ ∘ h) v }, x.ambient⟩
      | none => x
  | lRaise n f ι κ v e hreach hf hl hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v (some e) }, x.ambient⟩
      | none => x
  | lDivertAbort n f ι κ v hreach hf hl ht, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v none }, x.ambient⟩
      | none => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading (κ ∘ h) v none }, x.ambient⟩
      | none => x
  | lLeave n f κ v hf hl ht, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v none }, x.ambient⟩
      | none => x
  | lUnload n f κ v o hf hl hg, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .inactive o }, x.ambient⟩
      | none => x

/-- The state reached by the step. -/
def next (st : Step s) : State N K E V := edit st (psi st s)

/-- **Faithful Equation (52).** Every step factors as `s' = edit (Ψ s)`. -/
theorem factorization (st : Step s) : next st = edit st (psi st s) := rfl

/-- A step's `Ψ` effect is confined to the fiber it acts on: iterator steps
are confined to their yielded `δ`, and `L-Unload` is confined to the result
of the accumulator. -/
def Confined : Step s → Prop
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep => ConfinedEffect s n δ
  | lFinish n f ι κ v δ h hreach hf hl ht hstep => ConfinedEffect s n δ
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep => ConfinedEffect s n δ
  | lUnload n f κ v o hf hl hg => ConfinedEffect s n (κ (State.fullCtx s))
  | _ => True

/-- A step's recomputed `Ψ` is confined at both `x` and `y`.  This is the
state-pair version of `Confined` needed when `Step.psi` is evaluated away
from the step's source state. -/
def PsiConfinedAt (st : Step s) (x y : State N K E V) : Prop :=
  match st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lUnload n f κ v o hf hl hg =>
      ConfinedEffect x n (κ (State.fullCtx x)) ∧
      ConfinedEffect y n (κ (State.fullCtx y))
  | _ => True

/-- `Step.psi` preserves duplicate-free names. -/
theorem psi_preserves_nodupKeys {s x : State N K E V} (st : Step s)
    (hn : NodupKeys x.reg) : NodupKeys (Step.psi st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj => simpa [Step.psi] using hn
  | oRetire n f hf => simpa [Step.psi] using hn
  | oRemove n f o hf hl hchild => simpa [Step.psi] using hn
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using hn
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using hn
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using hn
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using hn
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.psi, hg] using State.writeEffect_preserves_nodupKeys hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.psi, hn'] using hn

/-- `Step.edit` preserves duplicate-free names. -/
theorem edit_preserves_nodupKeys {s x : State N K E V} (st : Step s)
    (hn : NodupKeys x.reg) : NodupKeys (Step.edit st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj =>
      simpa [Step.edit] using nodupKeys_set x.reg n
        (Fiber.mk c p (fun _ => none) false (.inactive none)) hn
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n { g with retired := true } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | oRemove n f o hf hl hchild =>
      simpa [Step.edit] using nodupKeys_del hn n
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .loading g.comp.iter id v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .loading ι' (κ ∘ h) v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .active (κ ∘ h) v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v (some e) } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading (κ ∘ h) v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .inactive o } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn

/-- `Step.psi` preserves pairwise disjointness of tables, assuming the
recomputed effect is confined at the input state. -/
theorem psi_preserves_pairwiseDisjointTables {s x : State N K E V} (st : Step s)
    (hnodup : NodupKeys x.reg) (hdisj : PairwiseDisjointTables x.reg)
    (hconf : Step.PsiConfinedAt st x x) :
    PairwiseDisjointTables (Step.psi st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj0 => simpa [Step.psi] using hdisj
  | oRetire n f hf => simpa [Step.psi] using hdisj
  | oRemove n f o hf hl hchild => simpa [Step.psi] using hdisj
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using hdisj
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using hdisj
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using hdisj
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using hdisj
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        have hconf' := hconf
        simpa [Step.psi, hg] using
          State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.psi, hn'] using hdisj

/-- `Step.edit` preserves pairwise disjointness of tables. -/
theorem edit_preserves_pairwiseDisjointTables {s x : State N K E V} (st : Step s)
    (hnodup : NodupKeys x.reg) (hdisj : PairwiseDisjointTables x.reg) :
    PairwiseDisjointTables (Step.edit st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj0 =>
      simpa [Step.edit] using pairwiseDisjointTables_set_empty hnodup hdisj
        (g := Fiber.mk c p (fun _ => none) false (.inactive none)) rfl
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with retired := true }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | oRemove n f o hf hl hchild =>
      simpa [Step.edit] using pairwiseDisjointTables_del hdisj n
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .loading g.comp.iter id v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .loading ι' (κ ∘ h) v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .active (κ ∘ h) v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v (some e) }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading (κ ∘ h) v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .inactive o }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj

/-- `Step.psi` never changes the lookup at a different name. -/
theorem psi_preserves_lookup_ne {s x : State N K E V} (st : Step s) {m : N}
    (hm : m ≠ st.name) : lookup (Step.psi st x).reg m = lookup x.reg m := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.psi]
  | oRetire n f hf => simp [Step.psi]
  | oRemove n f o hf hl hchild => simp [Step.psi]
  | lBegin n f v hf hl ht htable => simp [Step.psi]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.psi]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.psi]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lLeave n f κ v hf hl ht => simp [Step.psi]
  | lUnload n f κ v o hf hl hg =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.psi, hg]
        unfold State.writeEffect
        rw [hg]
        exact lookup_set_ne x.reg n m
          { g with table := splitTable g.comp.prov (κ (State.fullCtx x)).2 } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.psi, State.writeEffect, hn]

/-- `Step.psi` preserves pointwise fiber agreement. -/
theorem psi_preserves_sameFiberAt {s x y : State N K E V} (st : Step s) {m : N}
    (h : SameFiberAt x y m) : SameFiberAt (Step.psi st x) (Step.psi st y) m := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi] using h
  | oRetire n f hf => simpa [Step.psi] using h
  | oRemove n f o hf hl hchild => simpa [Step.psi] using h
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using h
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using h
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using h
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using h
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
        by_cases hy : (lookup y.reg n).isSome
        · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          simp [Step.psi, hgx, hgy]
          exact State.writeEffect_preserves_sameFiberAt (n := n)
            (δx := κ (State.fullCtx x)) (δy := κ (State.fullCtx y)) h
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.psi, hgx, hyn]
          exact State.writeEffect_preserves_sameFiberAt_left (n := n)
            (δ := κ (State.fullCtx x)) h
      · have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        by_cases hy : (lookup y.reg n).isSome
        · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          simp [Step.psi, hxn, hgy]
          exact State.writeEffect_preserves_sameFiberAt_right (n := n)
            (δ := κ (State.fullCtx y)) h
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.psi, hxn, hyn]
          exact h

/-- `Step.edit` never changes the lookup at a different name. -/
theorem edit_preserves_lookup_ne {s x : State N K E V} (st : Step s) {m : N}
    (hm : m ≠ st.name) : lookup (Step.edit st x).reg m = lookup x.reg m := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      simp [Step.edit]
      exact lookup_set_ne x.reg n m (Fiber.mk c p (fun _ => none) false (.inactive none)) hm'
  | oRetire n f hf =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with retired := true } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | oRemove n f o hf hl hchild =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      simp [Step.edit]
      exact lookup_del_ne (r := x.reg) (n := n) (m := m) hm'
  | lBegin n f v hf hl ht htable =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .loading g.comp.iter id v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .loading ι' (κ ∘ h) v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .active (κ ∘ h) v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v (some e) } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading (κ ∘ h) v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lLeave n f κ v hf hl ht =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lUnload n f κ v o hf hl hg =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .inactive o } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]

/-- `Step.edit` preserves pointwise fiber agreement. -/
theorem edit_preserves_sameFiberAt {s x y : State N K E V} (st : Step s) {m : N}
    (h : SameFiberAt x y m) : SameFiberAt (Step.edit st x) (Step.edit st y) m := by
  by_cases hmn : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj =>
        simpa [Step.edit] using set_preserves_sameFiberAt (n := n)
          (g := Fiber.mk c p (fun _ => none) false (.inactive none)) h
    | oRetire n f hf =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with retired := true }) (gy := { gy with retired := true }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | oRemove n f o hf hl hchild =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        simp [Step.edit, lookup_del_self]
    | lBegin n f v hf hl ht htable =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .loading gx.comp.iter id v })
            (gy := { gy with lc := .loading gy.comp.iter id v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .loading ι' (κ ∘ hh) v })
            (gy := { gy with lc := .loading ι' (κ ∘ hh) v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .active (κ ∘ hh) v })
            (gy := { gy with lc := .active (κ ∘ hh) v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lRaise n f ι κ v e hreach hf hl hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v (some e) })
            (gy := { gy with lc := .unloading κ v (some e) }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lDivertAbort n f ι κ v hreach hf hl ht =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v none })
            (gy := { gy with lc := .unloading κ v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading (κ ∘ hh) v none })
            (gy := { gy with lc := .unloading (κ ∘ hh) v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lLeave n f κ v hf hl ht =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v none })
            (gy := { gy with lc := .unloading κ v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lUnload n f κ v o hf hl hg =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .inactive o })
            (gy := { gy with lc := .inactive o }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
  · have hx_lookup : lookup (Step.edit st x).reg m = lookup x.reg m :=
      Step.edit_preserves_lookup_ne st hmn
    have hy_lookup : lookup (Step.edit st y).reg m = lookup y.reg m :=
      Step.edit_preserves_lookup_ne st hmn
    unfold SameFiberAt
    rw [hx_lookup, hy_lookup]
    exact h

/-- For a non-insert, non-remove step, `edit` agrees with the input state at
the acting name up to `SameFiberAt`. -/
theorem edit_preserves_sameFiberAt_self_of_not_insert_remove {s x : State N K E V}
    (st : Step s) (hno_insert : st.kind ≠ Full.StepKind.oInsert)
    (hno_remove : st.kind ≠ Full.StepKind.oRemove) :
    SameFiberAt (Step.edit st x) x st.name := by
  cases st with
  | oInsert n c p hn hp hdisj => exact False.elim (hno_insert (by simp [Step.kind]))
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | oRemove n f o hf hl hchild => exact False.elim (hno_remove (by simp [Step.kind]))
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]

/-- If a step is confined at its source state, then `PsiConfinedAt` holds
with both arguments equal to that source state. -/
theorem psiConfinedAt_self_of_confined {s : State N K E V} (st : Step s)
    (hconf : Step.Confined st) : Step.PsiConfinedAt st s s := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lUnload n f κ v o hf hl hg =>
      simpa [Step.Confined, Step.PsiConfinedAt] using hconf
  | _ => trivial

/-- If `PsiConfinedAt` holds for a pair with equal full contexts, it also
holds for the left state paired with itself. -/
theorem psiConfinedAt_self_of_pair_left {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hconf : Step.PsiConfinedAt st x y) : Step.PsiConfinedAt st x x := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lUnload n f κ v o hf hl hg =>
      exact ⟨hconf.1, hconf.1⟩
  | _ => trivial

/-- If `PsiConfinedAt` holds for a pair with equal full contexts, it also
holds for the right state paired with itself. -/
theorem psiConfinedAt_self_of_pair_right {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hconf : Step.PsiConfinedAt st x y) : Step.PsiConfinedAt st y y := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lUnload n f κ v o hf hl hg =>
      exact ⟨hconf.2, hconf.2⟩
  | _ => trivial

/-- `Step.next` preserves duplicate-free names. -/
theorem next_preserves_nodupKeys {s : State N K E V} (st : Step s)
    (hn : NodupKeys s.reg) : NodupKeys (Step.next st).reg := by
  rw [Step.factorization]
  exact Step.edit_preserves_nodupKeys st (Step.psi_preserves_nodupKeys st hn)

/-- `Step.next` preserves pairwise disjointness of tables, provided the
step's `Ψ` effect is confined at the source state. -/
theorem next_preserves_pairwiseDisjointTables {s : State N K E V} (st : Step s)
    (hnodup : NodupKeys s.reg) (hdisj : PairwiseDisjointTables s.reg)
    (hconf : Step.Confined st) : PairwiseDisjointTables (Step.next st).reg := by
  rw [Step.factorization]
  exact Step.edit_preserves_pairwiseDisjointTables st
    (Step.psi_preserves_nodupKeys st hnodup)
    (Step.psi_preserves_pairwiseDisjointTables st hnodup hdisj
      (Step.psiConfinedAt_self_of_confined st hconf))

end Step

/-! ## Faithful `≈` and type-level traces -/

namespace State

/-- The raw table read from a state at a name; an absent name reads as the
empty table. -/
def tableAt (s : State N K E V) (n : N) : CoefCtx K V :=
  match lookup s.reg n with
  | some f => f.table
  | none => fun _ => none

/-- `tableAt` is unchanged by deleting a different name. -/
theorem tableAt_del_ne {r : Registry N K V E} {n m : N} {a : CoefCtx K V}
    (hne : m ≠ n) :
    State.tableAt ⟨del r n, a⟩ m = State.tableAt ⟨r, a⟩ m := by
  simp [State.tableAt, lookup_del_ne hne]

/-- `rawSigma` of a cons is the head table union the tail. -/
theorem rawSigma_cons {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (p : N × Fiber N K V E) (rest : Registry N K V E) (k : K) :
    rawSigma (p :: rest) k = (p.2.table k <|> rawSigma rest k) := by
  rfl

/-- Under pairwise disjoint tables, the head table and the table at another
name cannot both be present. -/
theorem tableAt_disjoint_head {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {p : N × Fiber N K V E} {rest : Registry N K V E}
    (hdisj : PairwiseDisjointTables (p :: rest)) {n : N} (hpn : p.1 ≠ n) (k : K) :
    p.2.table k = none ∨ State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n k = none := by
  by_cases hlook : (lookup rest n).isSome
  · rcases Option.isSome_iff_exists.mp hlook with ⟨f, hf⟩
    have hmem : (n, f) ∈ rest := lookup_some_mem hf
    have hdisj' := hdisj p (by simp) (n, f) (by simp [hmem]) (by
      intro hEq
      apply hpn
      exact hEq)
    rcases hdisj' k with hnone | hnone'
    · exact Or.inl hnone
    · right
      simp [State.tableAt, hf]
      exact hnone'
  · have hn : lookup rest n = none := Option.not_isSome_iff_eq_none.mp hlook
    right
    simp [State.tableAt, hn]

/-- Deleting a name splits `rawSigma` into that name's table and the rest,
provided distinct fibers have disjoint tables. -/
theorem rawSigma_del_eq_of_disjoint {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} (r : Registry N K V E) (hn : NodupKeys r)
    (hdisj : PairwiseDisjointTables r) (n : N) (k : K) :
    rawSigma r k = (State.tableAt ⟨r, (fun _ => none : CoefCtx K V)⟩ n k <|> rawSigma (del r n) k) := by
  induction r with
  | nil => simp [rawSigma, del, State.tableAt, lookup]
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').2
      have hdisjrest : PairwiseDisjointTables rest := by
        intro a ha b hb hab k
        exact hdisj a (by simp [ha]) b (by simp [hb]) hab k
      by_cases h : p.1 = n
      · have hnot : p.1 ∉ rest.map (fun x => x.1) := by
          have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
            simpa [NodupKeys] using hn
          exact (List.nodup_cons.mp hn').1
        have hdel_rest : del rest n = rest := by
          apply del_eq_self_of_not_mem
          simpa [h] using hnot
        rw [rawSigma_cons p rest k]
        rw [show del (p :: rest) n = rest by simp [del, h, hdel_rest]]
        rw [show State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n =
            p.2.table by simp [State.tableAt, lookup, h]]
      · have ih' := ih hnrest hdisjrest
        rw [rawSigma_cons p rest k]
        rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        rw [show State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n =
            State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n by
              simp [State.tableAt, lookup, h]]
        rw [rawSigma_cons p (del rest n) k]
        rw [ih']
        have hdisjhead := tableAt_disjoint_head hdisj h k
        rcases hdisjhead with ha | hb
        · simp [ha]
        · simp [hb]

/-- If two duplicate-free, pairwise-disjoint registries have the same
`tableAt` at every name, then their raw sigmas agree. -/
theorem rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint {N : Type} [DecidableEq N]
    {K : Type} [DecidableEq K] {V : K → Type u} {E : Type}
    {r r' : Registry N K V E}
    (hn : NodupKeys r) (hn' : NodupKeys r')
    (hdisj : PairwiseDisjointTables r) (hdisj' : PairwiseDisjointTables r')
    (h : ∀ n, State.tableAt ⟨r, (fun _ => none : CoefCtx K V)⟩ n =
              State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ n) :
    rawSigma r = rawSigma r' := by
  funext k
  induction r generalizing r' with
  | nil =>
      have hnone : rawSigma r' k = none := rawSigma_eq_none_of_all_none (fun p hp => by
        have hk := congrFun (h p.1) k
        have hlook := lookup_self_of_mem_of_nodup hn' hp
        simp [State.tableAt, hlook] at hk
        exact hk.symm)
      simpa [rawSigma] using hnone.symm
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').2
      have hdisjrest : PairwiseDisjointTables rest := by
        intro a ha b hb hab k
        exact hdisj a (by simp [ha]) b (by simp [hb]) hab k
      have hnot : p.1 ∉ rest.map (fun x => x.1) := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').1
      have hp_lookup : lookup (p :: rest) p.1 = some p.2 := lookup_self_of_mem_of_nodup hn (by simp)
      have htable_r : State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ p.1 = p.2.table := by
        simp [State.tableAt, hp_lookup]
      have htable_eq : State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ p.1 k = p.2.table k := by
        have heq := congrFun (h p.1) k
        rw [htable_r] at heq
        exact heq.symm
      have hrest_table : ∀ n, State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n =
          State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ n := by
        intro n
        funext k
        by_cases hpn : n = p.1
        · subst n
          have hrest_none : State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ p.1 = fun _ => none := by
            simp [State.tableAt, lookup_none_of_not_mem hnot]
          have hdel_none : State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ p.1 = fun _ => none := by
            simp [State.tableAt, lookup_del_self]
          simp [hrest_none, hdel_none]
        · have hrest_eq : State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n =
            State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n := by
              simp [State.tableAt, lookup, hpn, Ne.symm hpn]
          have hdel_eq : State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ n =
              State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ n := by
                exact State.tableAt_del_ne (n := p.1) (m := n) hpn
          rw [hrest_eq, hdel_eq, h n]
      have ih' := ih (r' := del r' p.1) hnrest (nodupKeys_del hn' p.1)
        hdisjrest (pairwiseDisjointTables_del hdisj' p.1) hrest_table
      rw [rawSigma_cons p rest k]
      rw [rawSigma_del_eq_of_disjoint r' hn' hdisj' p.1 k]
      rw [htable_eq]
      rw [ih']

/-- **Faithful `≈`.** Two states agree on the ambient context and on every
name's raw table, while control fields may differ. -/
structure Approx (s s' : State N K E V) : Prop where
  ambient : s.ambient = s'.ambient
  tables : ∀ n, State.tableAt s n = State.tableAt s' n

namespace Approx

theorem refl (s : State N K E V) : State.Approx s s :=
  ⟨rfl, fun _ => rfl⟩

theorem symm {s s' : State N K E V} (h : State.Approx s s') : State.Approx s' s :=
  ⟨h.ambient.symm, fun n => (h.tables n).symm⟩

theorem trans {s s' s'' : State N K E V} (h : State.Approx s s')
    (h' : State.Approx s' s'') : State.Approx s s'' :=
  ⟨h.ambient.trans h'.ambient, fun n => (h.tables n).trans (h'.tables n)⟩

end Approx

/-- Under duplicate-freeness and pairwise disjoint tables, `≈` implies
`fullCtx` equality. -/
theorem fullCtx_of_nodup_of_disjoint {s t : State N K E V}
    (hs : NodupKeys s.reg) (ht : NodupKeys t.reg)
    (hdisjs : PairwiseDisjointTables s.reg) (hdisjt : PairwiseDisjointTables t.reg)
    (h : State.Approx s t) : State.fullCtx s = State.fullCtx t := by
  apply Prod.ext
  · exact h.ambient
  · exact rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint hs ht hdisjs hdisjt h.tables

/-- `ConfinedEffect` transfers from `y` to an `≈`-equivalent state `z`
with the same fiber at the acting name. -/
theorem confinedEffect_transfer_of_approx {y z : State N K E V} {m : N}
    {δ : Ctx K V}
    (hyz : State.Approx y z)
    (hfull : State.fullCtx y = State.fullCtx z)
    (hdom : (lookup y.reg m).isSome ↔ (lookup z.reg m).isSome)
    (hprov : ∀ gy gz, lookup y.reg m = some gy → lookup z.reg m = some gz →
      gy.comp.prov = gz.comp.prov)
    (hnody : NodupKeys y.reg) (hnodz : NodupKeys z.reg)
    (hconf : ConfinedEffect y m δ) :
    ConfinedEffect z m δ := by
  rcases hconf with ⟨fy, hfy, hout, hsupport, hdisj⟩
  have hz_some : (lookup z.reg m).isSome := by
    rw [← hdom]
    exact Option.isSome_iff_exists.mpr ⟨fy, hfy⟩
  rcases Option.isSome_iff_exists.mp hz_some with ⟨fz, hfz⟩
  have hprov_eq : fz.comp.prov = fy.comp.prov := (hprov fy fz hfy hfz).symm
  refine ⟨fz, hfz, ?_, ?_, ?_⟩
  · intro k hk
    have hk_y : k ∉ fy.comp.prov := by simpa [hprov_eq] using hk
    have hraw : rawSigma y.reg k = rawSigma z.reg k := by
      have hsnd := congrArg Prod.snd hfull
      exact congrFun hsnd k
    exact (hraw.symm.trans (hout k hk_y))
  · intro k hk
    have hk_y : k ∉ fy.comp.prov := by simpa [hprov_eq] using hk
    have htable_z_symm : fy.table = fz.table := by
      simpa [State.tableAt, hfy, hfz] using hyz.tables m
    have htable_z : fz.table = fy.table := htable_z_symm.symm
    rw [htable_z]
    exact hsupport k hk_y
  · intro p hp hpm k hk
    have hk_y : k ∈ fy.comp.prov := by simpa [hprov_eq] using hk
    have hlook_z : lookup z.reg p.1 = some p.2 := lookup_self_of_mem_of_nodup hnodz hp
    have htable_yz : State.tableAt y p.1 k = State.tableAt z p.1 k := congrFun (hyz.tables p.1) k
    have hz_table : State.tableAt z p.1 k = p.2.table k := by
      simp [State.tableAt, hlook_z]
    have htable_eq : State.tableAt y p.1 k = p.2.table k := htable_yz.trans hz_table
    by_cases hy : (lookup y.reg p.1).isSome
    · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
      have htable_y : State.tableAt y p.1 k = gy.table k := by
        simp [State.tableAt, hgy]
      have hp_eq : p.2.table k = gy.table k := (htable_y.symm.trans htable_eq).symm
      have hp_y : (p.1, gy) ∈ y.reg := lookup_some_mem hgy
      have hnone : gy.table k = none := hdisj (p.1, gy) hp_y (by intro heq; exact hpm heq) k hk_y
      rw [hp_eq, hnone]
    · have hyn : lookup y.reg p.1 = none := Option.not_isSome_iff_eq_none.mp hy
      have htable_y : State.tableAt y p.1 k = none := by
        simp [State.tableAt, hyn]
      exact (htable_y.symm.trans htable_eq).symm

/-- A write-confined iterator still produces a confined effect after
recovering another fiber `n`. -/
theorem confinedEffect_of_confinedIterator_of_recover {s : State N K E V}
    {m n : N} {ι : Iterator (Ctx K V) E} {δ δ₀ : Ctx K V}
    (hmn : m ≠ n) (hnodup : NodupKeys s.reg)
    (hconf : ConfinedEffect s m δ₀)
    (hι : ∀ f, lookup s.reg m = some f → ConfinedIterator ι f.comp.prov)
    (hstep : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ, h, c)) :
    ConfinedEffect (State.recover s n) m δ := by
  rcases hconf with ⟨f, hf, hout₀, hsupport, hdisj⟩
  have hfrec : lookup (State.recover s n).reg m = some f := by
    rw [State.lookup_recover_ne (n := n) (m := m) (Ne.symm hmn), hf]
  have hdisjrec := recover_preserves_confined_disjoint (m := m) (n := n) (f := f) hmn hnodup hf hdisj
  exact confinedEffect_of_confinedIterator hfrec (hι f hf) hstep hsupport hdisjrec

/-- A write-confined accumulator still produces a confined effect after
recovering another fiber `n`. -/
theorem confinedEffect_of_confinedAcc_of_recover {s : State N K E V}
    {m n : N} {κ : Ctx K V → Ctx K V} {δ₀ : Ctx K V}
    (hmn : m ≠ n) (hnodup : NodupKeys s.reg)
    (hconf : ConfinedEffect s m δ₀)
    (hκ : ∀ f, lookup s.reg m = some f → ConfinedAcc κ f.comp.prov) :
    ConfinedEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
  rcases hconf with ⟨f, hf, hout₀, hsupport, hdisj⟩
  have hfrec : lookup (State.recover s n).reg m = some f := by
    rw [State.lookup_recover_ne (n := n) (m := m) (Ne.symm hmn), hf]
  have hdisjrec := recover_preserves_confined_disjoint (m := m) (n := n) (f := f) hmn hnodup hf hdisj
  exact confinedEffect_of_confinedAcc hfrec (hκ f hf) hsupport hdisjrec

/-- `tableAt` after a pointwise `set` at the updated name. -/
theorem tableAt_set_eq (r : Registry N K V E) (n : N) (g : Fiber N K V E)
    (a : CoefCtx K V) :
    State.tableAt ⟨set r n g, a⟩ n = g.table := by
  simp [State.tableAt, lookup_set_eq]

/-- `tableAt` after a pointwise `set` away from the updated name. -/
theorem tableAt_set_ne (r : Registry N K V E) (n m : N) (g : Fiber N K V E)
    (a : CoefCtx K V) (hmn : m ≠ n) :
    State.tableAt ⟨set r n g, a⟩ m = State.tableAt ⟨r, a⟩ m := by
  simp [State.tableAt, lookup_set_ne r n m g hmn]

/-- `writeEffect` at the same name preserves `≈`, provided the acting name
has the same presence and the same provision in both input states. -/
theorem writeEffect_preserves_approx {x y : State N K E V} {n : N}
    (h : State.Approx x y) (δ : Ctx K V)
    (hdom : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome)
    (hprov : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
      gx.comp.prov = gy.comp.prov) :
    State.Approx (State.writeEffect x n δ) (State.writeEffect y n δ) := by
  constructor
  · unfold State.writeEffect
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      simp [hfx, hfy]
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [hxn, hyn, h.ambient]
  · intro m
    unfold State.writeEffect
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      by_cases hmn : m = n
      · subst m
        simp [State.tableAt, hfx, hfy, lookup_set_eq, hprov fx fy hfx hfy]
      · rw [hfx, hfy]
        rw [State.tableAt_set_ne x.reg n m
          (Fiber.mk fx.comp fx.parent (splitTable fx.comp.prov δ.2) fx.retired fx.lc) δ.1 hmn]
        rw [State.tableAt_set_ne y.reg n m
          (Fiber.mk fy.comp fy.parent (splitTable fy.comp.prov δ.2) fy.retired fy.lc) δ.1 hmn]
        exact h.tables m
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [State.tableAt, hxn, hyn]
      exact h.tables m

/-- `recover` at `n` does not change the raw table at a different name. -/
theorem tableAt_recover_ne {s : State N K E V} {n m : N}
    (hmn : n ≠ m) :
    State.tableAt (State.recover s n) m = State.tableAt s m := by
  unfold State.tableAt
  rw [State.lookup_recover_ne hmn]

/-- `recover` at an installed (non-inactive) fiber empties that fiber's
table. -/
theorem tableAt_recover_eq_of_not_inactive {s : State N K E V} {n : N}
    {f : Fiber N K V E} (hf : lookup s.reg n = some f)
    (hni : ∀ o, f.lc ≠ .inactive o) :
    State.tableAt (State.recover s n) n = fun _ => none := by
  unfold State.recover
  rw [hf]
  cases hlc : f.lc with
  | inactive o => exact False.elim (hni o hlc)
  | loading i κ v => simp [State.tableAt, lookup_set_eq, hlc]
  | active κ v => simp [State.tableAt, lookup_set_eq, hlc]
  | unloading κ v o => simp [State.tableAt, lookup_set_eq, hlc]

/-- `writeEffect` at a present fiber writes the split table at that fiber. -/
theorem tableAt_writeEffect_eq {s : State N K E V} {m : N} {g : Fiber N K V E}
    (hg : lookup s.reg m = some g) (δ : Ctx K V) :
    State.tableAt (State.writeEffect s m δ) m = splitTable g.comp.prov δ.2 := by
  unfold State.writeEffect
  rw [hg]
  exact State.tableAt_set_eq s.reg m { g with table := splitTable g.comp.prov δ.2 } δ.1

/-- `writeEffect` at `m` does not change the raw table at another name. -/
theorem tableAt_writeEffect_ne {s : State N K E V} {m x : N} {g : Fiber N K V E}
    (hg : lookup s.reg m = some g) (hmx : x ≠ m) (δ : Ctx K V) :
    State.tableAt (State.writeEffect s m δ) x = State.tableAt s x := by
  unfold State.writeEffect
  rw [hg]
  exact State.tableAt_set_ne s.reg m x { g with table := splitTable g.comp.prov δ.2 } δ.1 hmx

/-- If the ambient of `κ_n δ` is `δ'.1` and the table split at `m` is
unchanged, then `recover n` commutes with `writeEffect m` for distinct
`n` and `m`, up to `≈`. -/
theorem recover_writeEffect_approx {s : State N K E V} {n m : N}
    (hmn : n ≠ m) (δ δ' : Ctx K V)
    (hnodup : NodupKeys s.reg)
    (hconfm : ConfinedEffect s m δ)
    (hamb : (State.accAt s n δ).1 = δ'.1)
    (htable : ∀ g, lookup s.reg m = some g →
      splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ'.2)
    {f : Fiber N K V E} (hf : lookup s.reg n = some f)
    (hni : ∀ o, f.lc ≠ .inactive o) :
    State.Approx (State.recover (State.writeEffect s m δ) n)
      (State.writeEffect (State.recover s n) m δ') := by
  have hlook : lookup (State.writeEffect s m δ).reg n = some f :=
    State.lookup_writeEffect_ne hmn hf δ
  constructor
  · -- ambient
    have hfull : State.fullCtx (State.writeEffect s m δ) = δ :=
      State.fullCtx_writeEffect_of_confined hnodup hconfm
    rcases hconfm with ⟨g, hg, _⟩
    cases hlc : f.lc with
    | inactive o => exact False.elim (hni o hlc)
    | loading i κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_loading_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_loading_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
    | active κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_active_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_active_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
    | unloading κ v o =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_unloading_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_unloading_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
  · -- tables
    cases hlc : f.lc with
    | inactive o => exact False.elim (hni o hlc)
    | loading i κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_loading_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_loading_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']
    | active κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_active_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_active_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']
    | unloading κ v o =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_unloading_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_unloading_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']

/-- **Theorem 61, faithful step commutation.**  If the component iterators of
`n` and of the step's acting fiber are independent, the accumulated maps lie
in the corresponding transformation monoids, and the tracked fiber `n` is
open with the withdrawal invariants, then full recovery at `n` commutes with
the step's `Ψ` up to `≈`. -/
theorem recover_psi_commute_approx_of_indep {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ f, lookup s.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : Iterator.InTransformMonoid (iterOf n) (State.accAt s n))
    (hm_mem : ∀ f, lookup s.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : NodupKeys s.reg)
    (hwithdraw : State.Withdraws s n)
    (hwithdraw_on : ∀ f, lookup s.reg st.name = some f →
        State.WithdrawsOn s n f.comp.prov)
    (hopen : ∃ f, lookup s.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf : Step.Confined st) :
    State.Approx (State.recover (Step.psi st s) n)
      (Step.psi st (State.recover s n)) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | oRetire m f hf =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | oRemove m f o hf hl hchild =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lBegin m f v hf hl ht htable =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, some ι') := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, none) := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lRaise m f ι κ v e hreach hf hl hstep =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, c) := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lLeave m f κ v hf hl ht =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lUnload m f κ v o hf hl hg =>
      have hne_m : n ≠ m := by simpa [Step.name] using hne
      have hconfm : ConfinedEffect s m (κ (State.fullCtx s)) := hconf
      have hpsi : Step.psi (Step.lUnload m f κ v o hf hl hg) s =
          State.writeEffect s m (κ (State.fullCtx s)) := by
        simp [Step.psi, hf]
      have hpsi' : Step.psi (Step.lUnload m f κ v o hf hl hg) (State.recover s n) =
          State.writeEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
        simp [Step.psi, State.lookup_recover_ne hne_m, hf]
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hκm_mem : Iterator.InTransformMonoid (iterOf m) κ := by
        have h := hm_mem f hf
        simpa [Step.name, Lifecycle.acc, hl, hiter'] using h
      have hcomm := hind'.1 hn_mem hκm_mem
      have hamb : (State.accAt s n (κ (State.fullCtx s))).1 =
          (κ (State.fullCtx (State.recover s n))).1 := by
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        exact h
      have hw : ∀ γ, splitTable f.comp.prov ((State.accAt s n γ).2) =
          splitTable f.comp.prov γ.2 := by
        have hw0 : ∀ γ, splitTable f.comp.prov ((Lifecycle.acc fn.lc γ).2) =
            splitTable f.comp.prov γ.2 := by
          simpa [State.WithdrawsOn, hfn] using hwithdraw_on f hf
        intro γ
        simpa [State.accAt, hfn] using hw0 γ
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov (κ (State.fullCtx s)).2 =
            splitTable g.comp.prov (κ (State.fullCtx (State.recover s n))).2 := by
        intro g hg
        have hgf : g = f :=
          (lookup_eq_of_nodup (r := s.reg) (n := m) (f := f) (g := g) hnodup hf hg).symm
        subst g
        rw [hwithdraw]
        have hcomm' := congrArg (fun g => (g (State.fullCtx s)).2) hcomm
        simp only [Function.comp_apply] at hcomm'
        have hsplit : splitTable f.comp.prov ((State.accAt s n (κ (State.fullCtx s))).2) =
            splitTable f.comp.prov ((κ (State.accAt s n (State.fullCtx s))).2) := by
          rw [hcomm']
        have hw' := hw (κ (State.fullCtx s))
        exact (hw'.symm.trans hsplit)
      exact State.recover_writeEffect_approx hne_m (κ (State.fullCtx s))
        (κ (State.fullCtx (State.recover s n))) hnodup hconfm hamb htable hfn hni

end State

/-- If every reachable iterator and lifecycle accumulator is write-confined,
then a step that is confined at its source remains `PsiConfinedAt` after
recovering another fiber and folding through `≈`-equivalent states. -/
theorem Step.psiConfinedAt_of_confined {s x : State N K E V} (st : Step s) {n : N}
    (hst : st.name ≠ n)
    (hconf : Step.Confined st)
    (hconf_iter : ∀ f, lookup s.reg st.name = some f →
        ∀ ι, Iterator.Reachable f.comp.iter ι → ConfinedIterator ι f.comp.prov)
    (hconf_acc : ∀ f, lookup s.reg st.name = some f →
        ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov)
    (hnodup_s : NodupKeys s.reg)
    (hx_approx : State.Approx (State.recover s n) x)
    (hfull : State.fullCtx (State.recover s n) = State.fullCtx x)
    (hdom : (lookup (State.recover s n).reg st.name).isSome ↔
      (lookup x.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup (State.recover s n).reg st.name = some gx →
      lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov)
    (hnrec : NodupKeys (State.recover s n).reg) (hnx : NodupKeys x.reg) :
    Step.PsiConfinedAt st (State.recover s n) x := by
  cases st with
  | oInsert m c p hn hp hdisj => trivial
  | oRetire m f hf => trivial
  | oRemove m f o hf hl hchild => trivial
  | lBegin m f v hf hl ht htable => trivial
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lRaise m f ι κ v e hreach hf hl hstep => trivial
  | lDivertAbort m f ι κ v hreach hf hl ht => trivial
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lLeave m f κ v hf hl ht => trivial
  | lUnload m f κ v o hf hl hg =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      have hκ : ∀ f', lookup s.reg m = some f' → ConfinedAcc κ f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        have hκ' : ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov := by simpa [Step.name] using hconf_acc f hf
        simpa [Lifecycle.acc, hl] using hκ'
      have hconf_y : ConfinedEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
        exact State.confinedEffect_of_confinedAcc_of_recover
          (s := s) (m := m) (n := n) (κ := κ) (δ₀ := κ (State.fullCtx s))
          hmn hnodup_s hconf hκ
      have hκ_eq : κ (State.fullCtx (State.recover s n)) = κ (State.fullCtx x) := by
        rw [hfull]
      have hconf_x : ConfinedEffect x m (κ (State.fullCtx x)) := by
        have hconf_x' : ConfinedEffect x m (κ (State.fullCtx (State.recover s n))) := by
          exact State.confinedEffect_transfer_of_approx
            (y := State.recover s n) (z := x) (m := m)
            (δ := κ (State.fullCtx (State.recover s n)))
            hx_approx hfull (by simpa [Step.name] using hdom) (by simpa [Step.name] using hprov) hnrec hnx hconf_y
        simpa [hκ_eq] using hconf_x'
      exact ⟨hconf_y, hconf_x⟩

/-- A faithful `Step.psi` preserves `≈` when the input full contexts agree
and the acting name has the same presence in both input states. -/
theorem Step.psi_preserves_approx {s x y : State N K E V} (st : Step s)
    (h : State.Approx x y)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hdom : (lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup x.reg st.name = some gx →
      lookup y.reg st.name = some gy → gx.comp.prov = gy.comp.prov) :
    State.Approx (Step.psi st x) (Step.psi st y) := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi] using h
  | oRetire n f hf => simpa [Step.psi] using h
  | oRemove n f o hf hl hchild => simpa [Step.psi] using h
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using h
  | lIter n f ι κ v ι' δ h' hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lFinish n f ι κ v δ h' hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using h
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using h
  | lDivertLand n f ι κ v δ h' c hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using h
  | lUnload n f κ v o hf hl hg =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      by_cases hx : (lookup x.reg n).isSome
      · have hy : (lookup y.reg n).isSome := hdom'.mp hx
        rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
        rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
        have hκ : κ (State.fullCtx x) = κ (State.fullCtx y) := by rw [hfull]
        simp [Step.psi, hfx, hfy, hκ]
        exact State.writeEffect_preserves_approx h (κ (State.fullCtx y)) hdom' hprov'
      · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom'.mpr hy)
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
        simp [Step.psi, hxn, hyn, h]

/-- A faithful `Step.psi` preserves `fullCtx` equality when the recomputed
step is confined at both input states. -/
theorem Step.psi_preserves_fullCtx {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hdom : (lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup x.reg st.name = some gx →
      lookup y.reg st.name = some gy → gx.comp.prov = gy.comp.prov)
    (hnx : NodupKeys x.reg) (hny : NodupKeys y.reg)
    (hconf : Step.PsiConfinedAt st x y) :
    State.fullCtx (Step.psi st x) = State.fullCtx (Step.psi st y) := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi, hfull]
  | oRetire n f hf => simpa [Step.psi, hfull]
  | oRemove n f o hf hl hchild => simpa [Step.psi, hfull]
  | lBegin n f v hf hl ht htable => simpa [Step.psi, hfull]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi, hfull]
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi, hfull]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lLeave n f κ v hf hl ht => simpa [Step.psi, hfull]
  | lUnload n f κ v o hf hl hg =>
      have hconf' := hconf
      by_cases hx : (lookup x.reg n).isSome
      · have hy : (lookup y.reg n).isSome := hdom.mp hx
        rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
        rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
        simp only [Step.psi, hfx, hfy]
        rw [← hfull]
        have hcy : ConfinedEffect y n (κ (State.fullCtx x)) := by
          simpa [hfull] using hconf'.2
        exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hcy
      · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
        simp [Step.psi, hxn, hyn, hfull]

/-- **Faithful Equation (52) up to `≈`.** For every rule except `O-Remove`,
the `edit` half writes only control fields. -/
theorem Step.edit_approx_psi_of_ne_remove {s : State N K E V} (st : Step s)
    (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.Approx (Step.next st) (Step.psi st s) := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      constructor
      · simp [Step.next, Step.edit, Step.psi]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hn, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, lookup_set_ne, hmn]
  | oRetire n f hf =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | oRemove n f o hf hl hchild =>
      simp [Step.kind] at hno
  | lBegin n f v hf hl ht htable =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lLeave n f κ v hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lUnload n f κ v o hf hl hg =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq, lookup_set_ne, hmn]

/-- `recover` preserves `≈` when the two input states agree on the lookup at
`n` and on the full context.  This is the version needed for `edit`-away
steps: the edit does not touch `n`, so recovery at `n` sees the same fiber
and the same full context. -/
theorem State.recover_preserves_approx_of_lookup_fullCtx {x y : State N K E V} {n : N}
    (h : State.Approx x y)
    (hlook : lookup x.reg n = lookup y.reg n)
    (hfull : State.fullCtx x = State.fullCtx y) :
    State.Approx (State.recover x n) (State.recover y n) := by
  by_cases hn : (lookup y.reg n).isSome
  · rcases Option.isSome_iff_exists.mp hn with ⟨f, hf⟩
    have hx : lookup x.reg n = some f := by rw [hlook]; exact hf
    cases hlc : f.lc with
    | inactive o =>
        simpa [State.recover, hx, hf, hlc] using h
    | loading i κ v =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_loading_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_loading_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
    | active κ v =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_active_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_active_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
    | unloading κ v o =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_unloading_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_unloading_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
  · have hnone : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hn
    have hxnone : lookup x.reg n = none := by rw [hlook]; exact hnone
    simpa [State.recover, hxnone, hnone] using h

/-- For a non-`O-Remove` step acting on a fiber other than `n`, the `edit`
half does not change the full context. -/
theorem State.fullCtx_next_eq_fullCtx_psi_of_ne_remove {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name) (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.fullCtx (Step.next st) = State.fullCtx (Step.psi st s) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi,
          rawSigma_set_empty_fiber_of_not_mem hn]
  | oRetire m f hf =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_retired_eq]
  | oRemove m f o hf hl hchild =>
      exact False.elim (hno (by simp [Step.kind]))
  | lBegin m f v hf hl ht htable =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lRaise m f ι κ v e hreach hf hl hstep =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lLeave m f κ v hf hl ht =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lUnload m f κ v o hf hl hg =>
      have hpsi : Step.psi (Step.lUnload m f κ v o hf hl hg) s =
          State.writeEffect s m (κ (State.fullCtx s)) := by
        simp [Step.psi, hf]
      have hf' : lookup (State.writeEffect s m (κ (State.fullCtx s))).reg m =
          some ({ f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf (κ (State.fullCtx s))
      simp [State.fullCtx] at hpsi hf'
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']

/-- For a non-`O-Remove` step acting on a fiber other than `n`, the `edit`
half does not touch `n` and does not change the full context, so recovery at
`n` commutes with the `edit` up to `≈`. -/
theorem State.recover_next_approx_recover_psi_of_ne_remove {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name) (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s) n) := by
  apply State.recover_preserves_approx_of_lookup_fullCtx
  · exact Step.edit_approx_psi_of_ne_remove st hno
  · cases st with
    | oInsert m c p hn hp hdisj =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hn, lookup_set_ne, hmn, Ne.symm hmn]
    | oRetire m f hf =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | oRemove m f o hf hl hchild =>
        exact False.elim (hno (by simp [Step.kind]))
    | lBegin m f v hf hl ht htable =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lRaise m f ι κ v e hreach hf hl hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lDivertAbort m f ι κ v hreach hf hl ht =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lLeave m f κ v hf hl ht =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lUnload m f κ v o hf hl hg =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, State.lookup_writeEffect_eq hf (κ (State.fullCtx s)),
          lookup_set_ne, hmn, Ne.symm hmn]
  · exact State.fullCtx_next_eq_fullCtx_psi_of_ne_remove st hne hno

/-- A faithful `L-Iter` step on `n` is invisible to `State.recover` up to
`≈`: the new inverse recovers the full context that the accumulator already
knew. -/
theorem Step.recover_self_lIter_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {ι' : Iterator (Ctx K V) E} {δ : Ctx K V}
    {h : Ctx K V → Ctx K V}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n = some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, some ι'))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .loading ι' (κ ∘ h) v }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .loading ι' (κ ∘ h) v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · -- ambient: `(κ ∘ h) (fullCtx next) = κ (fullCtx s)`
    simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · -- tables: both recoveries empty `n`'s table
    intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-Finish` step on `n` is invisible to `State.recover` up to
`≈`. -/
theorem Step.recover_self_lFinish_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V} {h : Ctx K V → Ctx K V}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n = some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, none))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .active (κ ∘ h) v }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .active (κ ∘ h) v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-DivertLand` step on `n` is invisible to `State.recover` up
to `≈`. -/
theorem Step.recover_self_lDivertLand_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V} {h : Ctx K V → Ctx K V}
    {c : Option (Iterator (Ctx K V) E)}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n ≠ some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, c))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .unloading (κ ∘ h) v none }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .unloading (κ ∘ h) v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-Unload` step on `n` is invisible to `State.recover` up to
`≈`, provided the accumulator withdraws the fiber's own table. -/
theorem Step.recover_self_lUnload_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {κ : Ctx K V → Ctx K V} {v : K → Option N} {o : Option E}
    (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o)
    (hg : ¬ relied s.reg n)
    (hno_prov : ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none) :
    State.Approx
      (State.recover (Step.next (Step.lUnload n f κ v o hf hl hg)) n)
      (State.recover s n) := by
  let δ : Ctx K V := κ (State.fullCtx s)
  have hwrite : State.writeEffect s n δ =
      ⟨set s.reg n { f with table := splitTable f.comp.prov δ.2 }, δ.1⟩ := by
    simp [State.writeEffect, hf]
  have hnext_eq : Step.next (Step.lUnload n f κ v o hf hl hg) =
      ⟨set s.reg n { f with table := splitTable f.comp.prov δ.2, lc := .inactive o }, δ.1⟩ := by
    rw [Step.next, Step.psi, hf]
    rw [hwrite]
    simp [Step.edit, lookup_set_eq, set_set_eq]
  have hrecover_next : State.recover (Step.next (Step.lUnload n f κ v o hf hl hg)) n =
      Step.next (Step.lUnload n f κ v o hf hl hg) := by
    rw [hnext_eq]
    simp [State.recover, lookup_set_eq]
  have hrecover_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_unloading_eq hf hl
  rw [hrecover_next, hnext_eq, hrecover_s]
  constructor
  · rfl
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq]
      funext k
      by_cases hk : k ∈ f.comp.prov
      · simp [splitTable, hk]
        change (κ (State.fullCtx s)).2 k = none
        exact hno_prov k hk
      · simp [splitTable, hk]
    · simp [State.tableAt, lookup_set_ne, hmn, Ne.symm hmn]

/-- A faithful `O-Insert` step on `n` is invisible to `State.recover` up to
`≈`: inserting an empty inactive fiber is the same as having no fiber. -/
theorem Step.recover_self_oInsert_approx {s : State N K E V} {n : N}
    {c : Component K V E} {p : Option N}
    (hn : lookup s.reg n = none)
    (hp : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f)
    (hdisj : ∀ n' f, lookup s.reg n' = some f →
      (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
    State.Approx (State.recover (Step.next (Step.oInsert n c p hn hp hdisj)) n)
      (State.recover s n) := by
  have hs : State.recover s n = s := by
    simp [State.recover, hn]
  have hnext : Step.next (Step.oInsert n c p hn hp hdisj) =
      ⟨set s.reg n (Fiber.mk c p (fun _ => none) false (.inactive none)), s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi]
  rw [hs, hnext]
  simp [State.recover, lookup_set_eq]
  constructor
  · rfl
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, hn, lookup_set_eq]
    · simp [State.tableAt, hn, lookup_set_ne, hmn]

/-- A faithful `L-Begin` step on `n` is invisible to `State.recover` up to
`≈`, because `L-Begin` can only start from an inactive fiber whose table is
empty. -/
theorem Step.recover_self_lBegin_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .inactive none)
    (ht : targetOf s.reg n = some v) (htable : f.table = fun _ => none) :
    State.Approx (State.recover (Step.next (Step.lBegin n f v hf hl ht htable)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lBegin n f v hf hl ht htable) =
      ⟨set s.reg n { f with lc := .loading f.comp.iter id v }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hf_next : lookup (Step.next (Step.lBegin n f v hf hl ht htable)).reg n =
      some ({ f with lc := .loading f.comp.iter id v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n = s := by
    simp [State.recover, hf, hl]
  have hrec_next : State.recover (Step.next (Step.lBegin n f v hf hl ht htable)) n =
      ⟨set (Step.next (Step.lBegin n f v hf hl ht htable)).reg n
        ({ f with lc := .loading f.comp.iter id v, table := fun _ => none } : Fiber N K V E),
        (State.fullCtx (Step.next (Step.lBegin n f v hf hl ht htable))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [State.fullCtx, rawSigma_set_lc_eq]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, hf, lookup_set_eq, set_set_eq, htable]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-Raise` step on `n` is invisible to `State.recover` up to
`≈`: it only changes the lifecycle to unloading, keeping the same
accumulator and the same table. -/
theorem Step.recover_self_lRaise_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {e : E}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (hstep : Iterator.step ι (State.fullCtx s) = .error e) :
    State.Approx (State.recover (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep) =
      ⟨set s.reg n { f with lc := .unloading κ v (some e) }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg n =
      some ({ f with lc := .unloading κ v (some e) } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_loading_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) n =
      ⟨set (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg n
        ({ f with lc := .unloading κ v (some e), table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-DivertAbort` step on `n` is invisible to `State.recover`
up to `≈`: it only changes the lifecycle to unloading. -/
theorem Step.recover_self_lDivertAbort_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n ≠ some v) :
    State.Approx (State.recover (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht) =
      ⟨set s.reg n { f with lc := .unloading κ v none }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg n =
      some ({ f with lc := .unloading κ v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_loading_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) n =
      ⟨set (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg n
        ({ f with lc := .unloading κ v none, table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-Leave` step on `n` is invisible to `State.recover` up to
`≈`: it only changes an active lifecycle to unloading. -/
theorem Step.recover_self_lLeave_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v)
    (ht : targetOf s.reg n ≠ some v) :
    State.Approx (State.recover (Step.next (Step.lLeave n f κ v hf hl ht)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lLeave n f κ v hf hl ht) =
      ⟨set s.reg n { f with lc := .unloading κ v none }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lLeave n f κ v hf hl ht)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lLeave n f κ v hf hl ht)).reg n =
      some ({ f with lc := .unloading κ v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_active_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lLeave n f κ v hf hl ht)) n =
      ⟨set (Step.next (Step.lLeave n f κ v hf hl ht)).reg n
        ({ f with lc := .unloading κ v none, table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lLeave n f κ v hf hl ht)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `O-Retire` step on `n` is invisible to `State.recover` up to
`≈`: retirement is a control field that `≈` forgets. -/
theorem Step.recover_self_oRetire_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E}
    (hf : lookup s.reg n = some f) :
    State.Approx (State.recover (Step.next (Step.oRetire n f hf)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.oRetire n f hf) =
      ⟨set s.reg n { f with retired := true }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.oRetire n f hf)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_retired_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.oRetire n f hf)).reg n =
      some ({ f with retired := true } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  cases hlc : f.lc with
  | inactive o =>
      have hrec_s : State.recover s n = s := by
        simp [State.recover, hf, hlc]
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          Step.next (Step.oRetire n f hf) := by
        simp [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · rfl
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, hf, lookup_set_eq]
        · simp [State.tableAt, hf, lookup_set_ne, hmn]
  | loading i κ v =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_loading_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]
  | active κ v =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_active_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]
  | unloading κ v o =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_unloading_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- For a self-step, the extra withdrawal condition needed by `L-Unload`: the
accumulator must leave every key in the fiber's own provision absent.  For
all other self-steps this predicate is trivially true. -/
def Step.SelfWithdrawsAt {s : State N K E V} (st : Step s) : Prop :=
  match st with
  | Step.lUnload n f κ v o hf hl hg =>
      ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none
  | _ => True

/-- A total self-step recovery lemma for every non-`O-Remove` rule.  The
iterator rules additionally require duplicate-free registries and confined
writes; `L-Unload` requires the withdrawal condition captured by
`SelfWithdrawsAt`. -/
theorem Step.recover_self_approx_of_confined {s : State N K E V} (st : Step s)
    {n : N}
    (hname : st.name = n)
    (hno : st.kind ≠ Full.StepKind.oRemove)
    (hnodup : NodupKeys s.reg)
    (hconf : Step.Confined st)
    (hw : Step.SelfWithdrawsAt st) :
    State.Approx (State.recover (Step.next st) n) (State.recover s n) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_oInsert_approx hn hp hdisj
  | oRetire m f hf =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_oRetire_approx hf
  | oRemove m f o hf hl hchild =>
      exact False.elim (hno (by simp [Step.kind]))
  | lBegin m f v hf hl ht htable =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lBegin_approx hf hl ht htable
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lIter_approx hreach hf hl ht hstep hnodup hconf'
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lFinish_approx hreach hf hl ht hstep hnodup hconf'
  | lRaise m f ι κ v e hreach hf hl hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lRaise_approx hreach hf hl hstep
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lDivertAbort_approx hreach hf hl ht
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lDivertLand_approx hreach hf hl ht hstep hnodup hconf'
  | lLeave m f κ v hf hl ht =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lLeave_approx hf hl ht
  | lUnload m f κ v o hf hl hg =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hw' : ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none := by
        simpa [Step.SelfWithdrawsAt] using hw
      exact Step.recover_self_lUnload_approx hf hl hg hw'

/-- Wrapper for presence agreement, used to avoid an elaboration issue with
local functions returning `Iff` directly. -/
def SamePresence {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  (lookup (State.recover s n).reg st.name).isSome ↔ (lookup x.reg st.name).isSome

/-- Wrapper for provision agreement, used to avoid an elaboration issue with
local functions returning `Iff` directly. -/
def SameProvision {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  ∀ gx gy, lookup (State.recover s n).reg st.name = some gx →
    lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov

/-- Combined presence/provision agreement for the fiber acted on by `st`.
This packages `SamePresence` and `SameProvision` into one side condition. -/
def SameFiber {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  match lookup (State.recover s n).reg st.name, lookup x.reg st.name with
  | some gx, some gy => gx.comp.prov = gy.comp.prov
  | none, none => True
  | _, _ => False

/-- `SameFiber` implies `SamePresence`. -/
theorem samePresence_of_sameFiber {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} (hf : SameFiber s n st x) : SamePresence s n st x := by
  unfold SamePresence
  unfold SameFiber at hf
  cases hrec : lookup (State.recover s n).reg st.name with
  | none =>
      cases hx : lookup x.reg st.name with
      | none => simp [hrec, hx]
      | some gy => simp [hrec, hx] at hf
  | some gx =>
      cases hx : lookup x.reg st.name with
      | none => simp [hrec, hx] at hf
      | some gy => simp [hrec, hx, hf]

/-- `SameFiber` implies `SameProvision`. -/
theorem sameProvision_of_sameFiber {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} (hf : SameFiber s n st x) : SameProvision s n st x := by
  intro gx gy hgx hgy
  unfold SameFiber at hf
  rw [hgx, hgy] at hf
  exact hf

/-- `SamePresence` and `SameProvision` together imply `SameFiber`. -/
theorem sameFiber_of_samePresence_sameProvision {s : State N K E V} {n : N}
    {st : Step s} {x : State N K E V}
    (hdom : SamePresence s n st x) (hprov : SameProvision s n st x) :
    SameFiber s n st x := by
  unfold SameFiber
  by_cases hx : (lookup (State.recover s n).reg st.name).isSome
  · have hy : (lookup x.reg st.name).isSome := hdom.mp hx
    rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
    rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
    simp [hgx, hgy]
    exact hprov gx gy hgx hgy
  · have hxn : lookup (State.recover s n).reg st.name = none :=
      Option.not_isSome_iff_eq_none.mp hx
    have hy : ¬ (lookup x.reg st.name).isSome := by
      intro hy
      exact hx (hdom.mpr hy)
    have hyn : lookup x.reg st.name = none := Option.not_isSome_iff_eq_none.mp hy
    simp [hxn, hyn]

/-- `SameFiber` is `SameFiberAt` after recovering `n`. -/
theorem sameFiber_eq_sameFiberAt {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} : SameFiber s n st x = SameFiberAt (State.recover s n) x st.name := by
  rfl

/-- A finite trace of faithful `Step` records. -/
inductive StepTrace : State N K E V → State N K E V → Type (max 1 u) where
  | nil (s : State N K E V) : StepTrace s s
  | cons {s₁ s₂ s₃ : State N K E V} (st : Step s₁) (hnext : Step.next st = s₂)
      (ht : StepTrace s₂ s₃) : StepTrace s₁ s₃

namespace StepTrace

/-- A predicate holds of every step in a type-level trace. -/
def AllSteps {s t : State N K E V}
    (P : ∀ {s : State N K E V}, Step s → Prop) :
    StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht => P st ∧ AllSteps P ht

/-- Fold the `Ψ` maps of a trace over a state. -/
def foldPsi {s t : State N K E V} :
    StepTrace s t → State N K E V → State N K E V
  | .nil _, x => x
  | .cons st _ ht, x => foldPsi ht (Step.psi st x)

/-- Fold the `Ψ` maps of a trace, skipping steps acting on `n`. -/
def foldPsiExcept {s t : State N K E V} (ht : StepTrace s t) (n : N)
    (x : State N K E V) : State N K E V :=
  match ht with
  | .nil _ => x
  | .cons st _ ht => foldPsiExcept ht n (if st.name = n then x else Step.psi st x)

/-- A trace never inserts a fiber other than `n`.  Together with the absence
of `O-Remove`, this keeps the folded state's non-`n` lookups aligned with the
trace's source states. -/
def NoNonNInsert {s t : State N K E V} (n : N) : StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht => (st.name = n ∨ st.kind ≠ Full.StepKind.oInsert) ∧ NoNonNInsert n ht

/-- Trace-local version of the `SameFiber` side condition: at every non-`n`
step, the folded state `x` has the same fiber (presence and provision) as the
step's source state. -/
def PsiFiberAgrees {s t : State N K E V} (n : N) (x : State N K E V) :
    StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      (st.name = n ∨ SameFiber s n st x) ∧
        PsiFiberAgrees n (if st.name = n then x else Step.psi st x) ht

/-- Trace-local version of the `PsiConfinedAt` side condition: at every
non-`n` step, the recomputed `Ψ` is confined at both the recovered source and
the current folded state. -/
def PsiConfinedAgrees {s t : State N K E V} (n : N) (x : State N K E V) :
    StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      (st.name = n ∨ Step.PsiConfinedAt st (State.recover s n) x) ∧
        PsiConfinedAgrees n (if st.name = n then x else Step.psi st x) ht

/-- If the folded state agrees with the trace's initial state on all non-`n`
fibers, no non-`n` fiber is inserted, and no fiber is removed, then
`PsiFiberAgrees` holds. -/
theorem PsiFiberAgrees_of_sameFiberAt {s t : State N K E V} (ht : StepTrace s t)
    {n : N} {x : State N K E V}
    (hx : ∀ m, m ≠ n → SameFiberAt s x m)
    (hno_insert : NoNonNInsert n ht)
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht) :
    PsiFiberAgrees n x ht := by
  induction ht generalizing x with
  | nil => trivial
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      rcases hno_insert with ⟨hst_insert, htail_insert⟩
      rcases hno_remove with ⟨hst_remove, htail_remove⟩
      constructor
      · by_cases hst : st.name = n
        · exact Or.inl hst
        · right
          have hx_st : SameFiberAt s₁ x st.name := hx st.name hst
          rw [sameFiber_eq_sameFiberAt]
          unfold SameFiberAt
          rw [State.lookup_recover_ne (n := n) (m := st.name) (Ne.symm hst)]
          exact hx_st
      · let x' : State N K E V := if st.name = n then x else Step.psi st x
        have hx' : ∀ m, m ≠ n → SameFiberAt (Step.next st) x' m := by
          intro m hm
          unfold x'
          by_cases hst : st.name = n
          · simp [hst]
            unfold SameFiberAt
            rw [Step.factorization]
            have hpsi : lookup (Step.psi st s₁).reg m = lookup s₁.reg m :=
              Step.psi_preserves_lookup_ne st (by simpa [hst] using hm)
            have hedit : lookup (Step.edit st (Step.psi st s₁)).reg m =
                lookup (Step.psi st s₁).reg m :=
              Step.edit_preserves_lookup_ne st (by simpa [hst] using hm)
            rw [hedit, hpsi]
            exact hx m hm
          · simp [hst]
            by_cases hm_st : m = st.name
            · subst m
              rw [Step.factorization]
              have hpsi : SameFiberAt (Step.psi st s₁) (Step.psi st x) st.name :=
                Step.psi_preserves_sameFiberAt st (hx st.name hst)
              have hno_i : st.kind ≠ Full.StepKind.oInsert := by
                rcases hst_insert with h_eq | h_no
                · exact False.elim (hst h_eq)
                · exact h_no
              have hno_r : st.kind ≠ Full.StepKind.oRemove := hst_remove
              have hedit_self : SameFiberAt (Step.edit st (Step.psi st s₁)) (Step.psi st s₁) st.name :=
                Step.edit_preserves_sameFiberAt_self_of_not_insert_remove st hno_i hno_r
              exact sameFiberAt_trans hedit_self hpsi
            · unfold SameFiberAt
              rw [Step.factorization]
              have hpsi_x : lookup (Step.psi st x).reg m = lookup x.reg m :=
                Step.psi_preserves_lookup_ne st (by exact hm_st)
              have hpsi_s : lookup (Step.psi st s₁).reg m = lookup s₁.reg m :=
                Step.psi_preserves_lookup_ne st (by exact hm_st)
              have hedit : lookup (Step.edit st (Step.psi st s₁)).reg m =
                  lookup (Step.psi st s₁).reg m :=
                Step.edit_preserves_lookup_ne st (by exact hm_st)
              rw [hpsi_x, hedit, hpsi_s]
              exact hx m hm
        have hx'' : ∀ m, m ≠ n → SameFiberAt s₂ x' m := by
          intro m hm
          simpa [hnext] using hx' m hm
        have htail := ih hx'' htail_insert htail_remove
        exact htail

/-- Derive `PsiConfinedAgrees` from write-confined iterators/accumulators,
fiber stability, and the `≈`-invariants used by recovery exactness. -/
theorem PsiConfinedAgrees_of_confined {s t : State N K E V} (ht : StepTrace s t)
    {n : N} {x : State N K E V}
    (hx_same : ∀ m, m ≠ n → SameFiberAt s x m)
    (hx_approx : State.Approx (State.recover s n) x)
    (hself : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover s' n))
    (hcomm : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      State.Approx (State.recover (Step.psi st s') n) (Step.psi st (State.recover s' n)))
    (hedit : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s') n))
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hno_insert : NoNonNInsert n ht)
    (hconf_non_self : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → Step.Confined st)
    (hconf_iter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        ∀ ι, Iterator.Reachable f.comp.iter ι → ConfinedIterator ι f.comp.prov)
    (hconf_acc : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov)
    (hnodup : ∀ (s' : State N K E V), NodupKeys s'.reg)
    (hdisj : ∀ (s' : State N K E V), PairwiseDisjointTables s'.reg) :
    PsiConfinedAgrees n x ht := by
  induction ht generalizing x with
  | nil => trivial
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      rcases hno_remove with ⟨hst_remove, htail_remove⟩
      rcases hno_insert with ⟨hst_insert, htail_insert⟩
      constructor
      · by_cases hst : st.name = n
        · exact Or.inl hst
        · right
          have hfiber : SameFiber s₁ n st x := by
            rw [sameFiber_eq_sameFiberAt]
            simpa [SameFiberAt, State.lookup_recover_ne (n := n) (m := st.name) (Ne.symm hst)]
              using hx_same st.name hst
          have hdom0 : SamePresence s₁ n st x := samePresence_of_sameFiber hfiber
          have hprov0 : SameProvision s₁ n st x := sameProvision_of_sameFiber hfiber
          have hfull : State.fullCtx (State.recover s₁ n) = State.fullCtx x := by
            exact State.fullCtx_of_nodup_of_disjoint (hnodup (State.recover s₁ n)) (hnodup x)
              (hdisj (State.recover s₁ n)) (hdisj x) hx_approx
          have hconf_head : Step.PsiConfinedAt st (State.recover s₁ n) x :=
            Step.psiConfinedAt_of_confined st hst (hconf_non_self s₁ st hst)
              (fun f hf ι hreach => hconf_iter s₁ st hst f hf ι hreach)
              (fun f hf => hconf_acc s₁ st hst f hf)
              (hnodup s₁) hx_approx hfull hdom0 hprov0
              (hnodup (State.recover s₁ n)) (hnodup x)
          exact hconf_head
      · let x' : State N K E V := if st.name = n then x else Step.psi st x
        have hx'_same : ∀ m, m ≠ n → SameFiberAt (Step.next st) x' m := by
          intro m hm
          unfold x'
          by_cases hst : st.name = n
          · simp [hst]
            unfold SameFiberAt
            rw [Step.factorization]
            have hpsi : lookup (Step.psi st s₁).reg m = lookup s₁.reg m :=
              Step.psi_preserves_lookup_ne st (by simpa [hst] using hm)
            have hedit' : lookup (Step.edit st (Step.psi st s₁)).reg m =
                lookup (Step.psi st s₁).reg m :=
              Step.edit_preserves_lookup_ne st (by simpa [hst] using hm)
            rw [hedit', hpsi]
            exact hx_same m hm
          · simp [hst]
            by_cases hm_st : m = st.name
            · subst m
              rw [Step.factorization]
              have hpsi : SameFiberAt (Step.psi st s₁) (Step.psi st x) st.name :=
                Step.psi_preserves_sameFiberAt st (hx_same st.name hst)
              have hno_i : st.kind ≠ Full.StepKind.oInsert := by
                rcases hst_insert with h_eq | h_no
                · exact False.elim (hst h_eq)
                · exact h_no
              have hno_r : st.kind ≠ Full.StepKind.oRemove := hst_remove
              have hedit_self : SameFiberAt (Step.edit st (Step.psi st s₁)) (Step.psi st s₁) st.name :=
                Step.edit_preserves_sameFiberAt_self_of_not_insert_remove st hno_i hno_r
              exact sameFiberAt_trans hedit_self hpsi
            · unfold SameFiberAt
              rw [Step.factorization]
              have hpsi_x : lookup (Step.psi st x).reg m = lookup x.reg m :=
                Step.psi_preserves_lookup_ne st (by exact hm_st)
              have hpsi_s : lookup (Step.psi st s₁).reg m = lookup s₁.reg m :=
                Step.psi_preserves_lookup_ne st (by exact hm_st)
              have hedit' : lookup (Step.edit st (Step.psi st s₁)).reg m =
                  lookup (Step.psi st s₁).reg m :=
                Step.edit_preserves_lookup_ne st (by exact hm_st)
              rw [hpsi_x, hedit', hpsi_s]
              exact hx_same m hm
        have hx'_same_s₂ : ∀ m, m ≠ n → SameFiberAt s₂ x' m := by
          intro m hm
          simpa [hnext] using hx'_same m hm
        have hx'_approx : State.Approx (State.recover s₂ n) x' := by
          unfold x'
          by_cases hst : st.name = n
          · simp [hst]
            have hself' := hself s₁ st hst hst_remove
            have hrec_eq : State.recover (Step.next st) n = State.recover s₂ n := by rw [hnext]
            rw [← hrec_eq]
            exact State.Approx.trans hself' hx_approx
          · simp [hst]
            have hfiber : SameFiber s₁ n st x := by
              rw [sameFiber_eq_sameFiberAt]
              simpa [SameFiberAt, State.lookup_recover_ne (n := n) (m := st.name) (Ne.symm hst)]
                using hx_same st.name hst
            have hdom0 : SamePresence s₁ n st x := samePresence_of_sameFiber hfiber
            have hprov0 : SameProvision s₁ n st x := sameProvision_of_sameFiber hfiber
            have hfull : State.fullCtx (State.recover s₁ n) = State.fullCtx x := by
              exact State.fullCtx_of_nodup_of_disjoint (hnodup (State.recover s₁ n)) (hnodup x)
                (hdisj (State.recover s₁ n)) (hdisj x) hx_approx
            have hpsi := Step.psi_preserves_approx st hx_approx hfull hdom0 hprov0
            have hcomm' := hcomm s₁ st hst
            have hedit' := hedit s₁ st hst hst_remove
            have hrec_eq : State.recover (Step.next st) n = State.recover s₂ n := by rw [hnext]
            rw [← hrec_eq]
            exact State.Approx.trans (State.Approx.trans hedit' hcomm') hpsi
        have htail := ih hx'_same_s₂ hx'_approx htail_remove htail_insert
        exact htail

/-- Trace-level faithful recovery exactness, engine.  The side conditions are
stated universally over the folded state so the induction can move from `x`
to `Step.psi st x` without re-proving them. -/
theorem recovery_exactness_aux {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} {s t : State N K E V} (ht : StepTrace s t) {n : N}
    (x : State N K E V)
    (hI : State.Approx (State.recover s n) x ∧
      State.fullCtx (State.recover s n) = State.fullCtx x)
    (hself : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover s' n))
    (hcomm : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      State.Approx (State.recover (Step.psi st s') n) (Step.psi st (State.recover s' n)))
    (hedit : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s') n))
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hfiber_trace : PsiFiberAgrees n x ht)
    (hnrec : ∀ (s' : State N K E V), NodupKeys (State.recover s' n).reg)
    (hnx : NodupKeys x.reg)
    (hdisjrec : ∀ (s' : State N K E V), PairwiseDisjointTables (State.recover s' n).reg)
    (hdisjx : PairwiseDisjointTables x.reg)
    (hconf_trace : PsiConfinedAgrees n x ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n x) := by
  induction ht generalizing x hnx hdisjx with
  | nil s =>
      simpa [StepTrace.foldPsiExcept] using hI.1
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      by_cases hst : st.name = n
      · rcases hno_remove with ⟨hno_self, htail_no⟩
        have hself' := hself s₁ st hst hno_self
        have hrec_eq : State.recover (Step.next st) n = State.recover s₂ n := by rw [hnext]
        have hfull_self : State.fullCtx (State.recover (Step.next st) n) =
            State.fullCtx (State.recover s₁ n) := by
          exact State.fullCtx_of_nodup_of_disjoint (hnrec (Step.next st)) (hnrec s₁)
            (hdisjrec (Step.next st)) (hdisjrec s₁) hself'
        have hI' : State.Approx (State.recover s₂ n) x ∧
            State.fullCtx (State.recover s₂ n) = State.fullCtx x := by
          constructor
          · rw [← hrec_eq]
            exact State.Approx.trans hself' hI.1
          · rw [← hrec_eq]
            exact hfull_self.trans hI.2
        rcases hfiber_trace with ⟨_, htail_fiber⟩
        rcases hconf_trace with ⟨_, htail_conf⟩
        have htail_fiber' : PsiFiberAgrees n x ht := by simpa [hst] using htail_fiber
        have htail_conf' : PsiConfinedAgrees n x ht := by simpa [hst] using htail_conf
        have htail := ih x hI' htail_no htail_fiber' hnx hdisjx htail_conf'
        simpa [StepTrace.foldPsiExcept, hst] using htail
      · have hno : st.kind ≠ Full.StepKind.oRemove := by
          rcases hno_remove with ⟨hno_rem, _⟩
          exact hno_rem
        have hrec_eq : State.recover (Step.next st) n = State.recover s₂ n := by rw [hnext]
        have hedit' := hedit s₁ st hst hno
        have hcomm' := hcomm s₁ st hst
        rcases hfiber_trace with ⟨hfiber_head, htail_fiber⟩
        rcases hconf_trace with ⟨hconf_head, htail_conf⟩
        have hfiber0 : SameFiber s₁ n st x := by
          rcases hfiber_head with hst_eq | hfiber0
          · exact False.elim (hst hst_eq)
          · exact hfiber0
        have hconf0 : Step.PsiConfinedAt st (State.recover s₁ n) x := by
          rcases hconf_head with hst_eq | hconf0
          · exact False.elim (hst hst_eq)
          · exact hconf0
        have hdom' : (lookup (State.recover s₁ n).reg st.name).isSome ↔
            (lookup x.reg st.name).isSome := by
          simpa [SamePresence] using (samePresence_of_sameFiber hfiber0)
        have hprov' : ∀ gx gy, lookup (State.recover s₁ n).reg st.name = some gx →
            lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov := by
          simpa [SameProvision] using (sameProvision_of_sameFiber hfiber0)
        have hpsi := Step.psi_preserves_approx st hI.1 hI.2 hdom' hprov'
        have hpsi_full := Step.psi_preserves_fullCtx st hI.2 hdom' hprov'
          (hnrec s₁) hnx hconf0
        have hfull_edit : State.fullCtx (State.recover (Step.next st) n) =
            State.fullCtx (State.recover (Step.psi st s₁) n) := by
          exact State.fullCtx_of_nodup_of_disjoint (hnrec (Step.next st))
            (hnrec (Step.psi st s₁))
            (hdisjrec (Step.next st)) (hdisjrec (Step.psi st s₁))
            hedit'
        have hpsi_rec_nodup : NodupKeys (Step.psi st (State.recover s₁ n)).reg :=
          Step.psi_preserves_nodupKeys st (hnrec s₁)
        have hpsi_rec_disj : PairwiseDisjointTables (Step.psi st (State.recover s₁ n)).reg := by
          have hconf_rec_self : Step.PsiConfinedAt st (State.recover s₁ n) (State.recover s₁ n) :=
            Step.psiConfinedAt_self_of_pair_left st hI.2 hconf0
          exact Step.psi_preserves_pairwiseDisjointTables st (hnrec s₁) (hdisjrec s₁) hconf_rec_self
        have hfull_comm : State.fullCtx (State.recover (Step.psi st s₁) n) =
            State.fullCtx (Step.psi st (State.recover s₁ n)) := by
          exact State.fullCtx_of_nodup_of_disjoint (hnrec (Step.psi st s₁))
            hpsi_rec_nodup
            (hdisjrec (Step.psi st s₁)) hpsi_rec_disj
            hcomm'
        have hx_nodup' : NodupKeys (Step.psi st x).reg := Step.psi_preserves_nodupKeys st hnx
        have hx_disj' : PairwiseDisjointTables (Step.psi st x).reg := by
          have hconf_x_self : Step.PsiConfinedAt st x x :=
            Step.psiConfinedAt_self_of_pair_right st hI.2 hconf0
          exact Step.psi_preserves_pairwiseDisjointTables st hnx hdisjx hconf_x_self
        have hI' : State.Approx (State.recover s₂ n) (Step.psi st x) ∧
            State.fullCtx (State.recover s₂ n) = State.fullCtx (Step.psi st x) := by
          constructor
          · rw [← hrec_eq]
            exact State.Approx.trans (State.Approx.trans hedit' hcomm') hpsi
          · rw [← hrec_eq]
            exact (hfull_edit.trans hfull_comm).trans hpsi_full
        have htail_no : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht := by
          rcases hno_remove with ⟨_, htail_no⟩
          exact htail_no
        have htail_fiber' : PsiFiberAgrees n (Step.psi st x) ht := by simpa [hst] using htail_fiber
        have htail_conf' : PsiConfinedAgrees n (Step.psi st x) ht := by simpa [hst] using htail_conf
        have htail := ih (Step.psi st x) hI' htail_no htail_fiber' hx_nodup' hx_disj' htail_conf'
        simpa [StepTrace.foldPsiExcept, hst] using htail

/-- Faithful Thm 61, trace-level statement with universally quantified side
conditions.  This is a valid formal statement; the concrete instantiation
still needs well-formedness preservation to discharge the universal side
conditions. -/
theorem recovery_exactness_recoverAcc {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} {s t : State N K E V} (ht : StepTrace s t)
    {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧
      f.lc = .loading f.comp.iter id v ∧ f.table = fun _ => none)
    (hself : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover s' n))
    (hcomm : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      State.Approx (State.recover (Step.psi st s') n) (Step.psi st (State.recover s' n)))
    (hedit : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s') n))
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hfiber_trace : PsiFiberAgrees n s ht)
    (hnrec : ∀ (s' : State N K E V), NodupKeys (State.recover s' n).reg)
    (hnx : NodupKeys s.reg)
    (hdisjrec : ∀ (s' : State N K E V), PairwiseDisjointTables (State.recover s' n).reg)
    (hdisjx : PairwiseDisjointTables s.reg)
    (hconf_trace : PsiConfinedAgrees n s ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n s) := by
  rcases hstart with ⟨f, hf, hl, htbl⟩
  have hrecover_id : State.recover s n = s := State.recover_of_loading_id hf htbl hl
  have hI : State.Approx (State.recover s n) s ∧
      State.fullCtx (State.recover s n) = State.fullCtx s := by
    constructor
    · rw [hrecover_id]
      exact State.Approx.refl s
    · rw [hrecover_id]
  exact StepTrace.recovery_exactness_aux ht s hI hself hcomm hedit hno_remove hfiber_trace
    hnrec hnx hdisjrec hdisjx hconf_trace

/-- **Corollary 62 (terminal recovery), faithful form.**  Given a trace in
which the tracked fiber `n` starts freshly loading, all other fibers are
independent and confined, `n` stays open throughout, and the same presence /
provision / nodup / disjointness / confined-at side conditions hold at every
folded state, the final state is `≈` to the result of folding only the other
fibers' `Ψ` maps.  This is the concrete hself/hcomm instantiation of
`recovery_exactness_recoverAcc`; discharging the well-formedness side
conditions from the operational invariants is the next step. -/
theorem recovery_exactness_cor62 {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} {s t : State N K E V} (ht : StepTrace s t)
    {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧
      f.lc = .loading f.comp.iter id v ∧ f.table = fun _ => none)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : ∀ (s' : State N K E V),
      Iterator.InTransformMonoid (iterOf n) (State.accAt s' n))
    (hm_mem : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : ∀ (s' : State N K E V), NodupKeys s'.reg)
    (hwithdraw : ∀ (s' : State N K E V), State.Withdraws s' n)
    (hwithdraw_on : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → State.WithdrawsOn s' n f.comp.prov)
    (hopen : ∀ (s' : State N K E V),
      ∃ f, lookup s'.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf_self : ∀ (s' : State N K E V) (st : Step s'), st.name = n → Step.Confined st)
    (hself_withdraw : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      Step.SelfWithdrawsAt st)
    (hconf_non_self : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → Step.Confined st)
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hfiber_trace : PsiFiberAgrees n s ht)
    (hnrec : ∀ (s' : State N K E V), NodupKeys (State.recover s' n).reg)
    (hnx : NodupKeys s.reg)
    (hdisjrec : ∀ (s' : State N K E V), PairwiseDisjointTables (State.recover s' n).reg)
    (hdisjx : PairwiseDisjointTables s.reg)
    (hconf_trace : PsiConfinedAgrees n s ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n s) := by
  have hself : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover s' n) := by
    intro s' st hname hno
    exact Step.recover_self_approx_of_confined st hname hno (hnodup s') (hconf_self s' st hname)
      (hself_withdraw s' st hname)
  have hcomm : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      State.Approx (State.recover (Step.psi st s') n) (Step.psi st (State.recover s' n)) := by
    intro s' st hst
    exact State.recover_psi_commute_approx_of_indep st (n := n) (Ne.symm hst) iterOf
      (hind s' st hst) (hiter s' st hst) (hn_mem s') (hm_mem s' st hst)
      (hnodup s') (hwithdraw s') (hwithdraw_on s' st hst) (hopen s')
      (hconf_non_self s' st hst)
  have hedit : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s') n) := by
    intro s' st hst hno
    exact State.recover_next_approx_recover_psi_of_ne_remove st (Ne.symm hst) hno
  exact StepTrace.recovery_exactness_recoverAcc ht hstart hself hcomm hedit hno_remove
    hfiber_trace hnrec hnx hdisjrec hdisjx hconf_trace

/-- Convenience form of Cor 62 where the global well-formedness assumptions
`NodupKeys` and `PairwiseDisjointTables` are used to discharge the four
redundant `recover`/folded-state side conditions. -/
theorem recovery_exactness_cor62_wellformed {N : Type} [DecidableEq N] {K : Type}
    [DecidableEq K] {E : Type} {V : K → Type u} {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧
      f.lc = .loading f.comp.iter id v ∧ f.table = fun _ => none)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : ∀ (s' : State N K E V),
      Iterator.InTransformMonoid (iterOf n) (State.accAt s' n))
    (hm_mem : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : ∀ (s' : State N K E V), NodupKeys s'.reg)
    (hdisj : ∀ (s' : State N K E V), PairwiseDisjointTables s'.reg)
    (hwithdraw : ∀ (s' : State N K E V), State.Withdraws s' n)
    (hwithdraw_on : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → State.WithdrawsOn s' n f.comp.prov)
    (hopen : ∀ (s' : State N K E V),
      ∃ f, lookup s'.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf_self : ∀ (s' : State N K E V) (st : Step s'), st.name = n → Step.Confined st)
    (hself_withdraw : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      Step.SelfWithdrawsAt st)
    (hconf_non_self : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → Step.Confined st)
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hfiber_trace : PsiFiberAgrees n s ht)
    (hconf_trace : PsiConfinedAgrees n s ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n s) := by
  exact StepTrace.recovery_exactness_cor62 ht hstart iterOf hind hiter hn_mem hm_mem hnodup
    hwithdraw hwithdraw_on hopen hconf_self hself_withdraw hconf_non_self hno_remove
    hfiber_trace
    (fun s' => State.recover_preserves_nodupKeys (hnodup s'))
    (hnodup s)
    (fun s' => State.recover_preserves_pairwiseDisjointTables (hnodup s') (hdisj s'))
    (hdisj s) hconf_trace

/-- Convenience form of Cor 62 that also derives `PsiFiberAgrees` from
`SameFiberAt` (reflexive at the start), `NoNonNInsert`, and `hno_remove`. -/
theorem recovery_exactness_cor62_fiber_stable {N : Type} [DecidableEq N] {K : Type}
    [DecidableEq K] {E : Type} {V : K → Type u} {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧
      f.lc = .loading f.comp.iter id v ∧ f.table = fun _ => none)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : ∀ (s' : State N K E V),
      Iterator.InTransformMonoid (iterOf n) (State.accAt s' n))
    (hm_mem : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : ∀ (s' : State N K E V), NodupKeys s'.reg)
    (hdisj : ∀ (s' : State N K E V), PairwiseDisjointTables s'.reg)
    (hwithdraw : ∀ (s' : State N K E V), State.Withdraws s' n)
    (hwithdraw_on : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → State.WithdrawsOn s' n f.comp.prov)
    (hopen : ∀ (s' : State N K E V),
      ∃ f, lookup s'.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf_self : ∀ (s' : State N K E V) (st : Step s'), st.name = n → Step.Confined st)
    (hself_withdraw : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      Step.SelfWithdrawsAt st)
    (hconf_non_self : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → Step.Confined st)
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hno_insert : NoNonNInsert n ht)
    (hconf_trace : PsiConfinedAgrees n s ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n s) := by
  have hfiber_trace : PsiFiberAgrees n s ht := by
    apply PsiFiberAgrees_of_sameFiberAt ht (n := n) (x := s)
    · intro m hm
      unfold SameFiberAt
      cases h : lookup s.reg m with
      | none => simp [h]
      | some g => simp [h]
    · exact hno_insert
    · exact hno_remove
  exact StepTrace.recovery_exactness_cor62_wellformed ht hstart iterOf hind hiter hn_mem hm_mem
    hnodup hdisj hwithdraw hwithdraw_on hopen hconf_self hself_withdraw hconf_non_self hno_remove
    hfiber_trace hconf_trace

/-- Convenience form of Cor 62 that derives both `PsiFiberAgrees` and
`PsiConfinedAgrees` from write-confined iterators/accumulators, fiber
stability, and the usual recovery-exactness invariants. -/
theorem recovery_exactness_cor62_confined {N : Type} [DecidableEq N] {K : Type}
    [DecidableEq K] {E : Type} {V : K → Type u} {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧
      f.lc = .loading f.comp.iter id v ∧ f.table = fun _ => none)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : ∀ (s' : State N K E V),
      Iterator.InTransformMonoid (iterOf n) (State.accAt s' n))
    (hm_mem : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : ∀ (s' : State N K E V), NodupKeys s'.reg)
    (hdisj : ∀ (s' : State N K E V), PairwiseDisjointTables s'.reg)
    (hwithdraw : ∀ (s' : State N K E V), State.Withdraws s' n)
    (hwithdraw_on : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → State.WithdrawsOn s' n f.comp.prov)
    (hopen : ∀ (s' : State N K E V),
      ∃ f, lookup s'.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf_self : ∀ (s' : State N K E V) (st : Step s'), st.name = n → Step.Confined st)
    (hself_withdraw : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      Step.SelfWithdrawsAt st)
    (hconf_non_self : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n → Step.Confined st)
    (hconf_iter : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f →
        ∀ ι, Iterator.Reachable f.comp.iter ι → ConfinedIterator ι f.comp.prov)
    (hconf_acc : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      ∀ f, lookup s'.reg st.name = some f → ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov)
    (hno_remove : StepTrace.AllSteps (fun {s'} (st : Step s') => st.kind ≠ Full.StepKind.oRemove) ht)
    (hno_insert : NoNonNInsert n ht) :
    State.Approx (State.recover t n) (StepTrace.foldPsiExcept ht n s) := by
  have hself : ∀ (s' : State N K E V) (st : Step s'), st.name = n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover s' n) := by
    intro s' st hname hno
    exact Step.recover_self_approx_of_confined st hname hno (hnodup s') (hconf_self s' st hname)
      (hself_withdraw s' st hname)
  have hcomm : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      State.Approx (State.recover (Step.psi st s') n) (Step.psi st (State.recover s' n)) := by
    intro s' st hst
    exact State.recover_psi_commute_approx_of_indep st (n := n) (Ne.symm hst) iterOf
      (hind s' st hst) (hiter s' st hst) (hn_mem s') (hm_mem s' st hst)
      (hnodup s') (hwithdraw s') (hwithdraw_on s' st hst) (hopen s')
      (hconf_non_self s' st hst)
  have hedit : ∀ (s' : State N K E V) (st : Step s'), st.name ≠ n →
      st.kind ≠ Full.StepKind.oRemove →
      State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s') n) := by
    intro s' st hst hno
    exact State.recover_next_approx_recover_psi_of_ne_remove st (Ne.symm hst) hno
  have hx_approx : State.Approx (State.recover s n) s := by
    rcases hstart with ⟨f, hf, hl, htbl⟩
    rw [State.recover_of_loading_id hf htbl hl]
    exact State.Approx.refl s
  have hconf_trace : PsiConfinedAgrees n s ht := by
    apply PsiConfinedAgrees_of_confined ht (n := n) (x := s)
    · intro m hm
      unfold SameFiberAt
      cases h : lookup s.reg m with
      | none => simp [h]
      | some g => simp [h]
    · exact hx_approx
    · exact hself
    · exact hcomm
    · exact hedit
    · exact hno_remove
    · exact hno_insert
    · exact hconf_non_self
    · intro s' st hst f hf ι hreach
      exact hconf_iter s' st hst f hf ι hreach
    · intro s' st hst f hf
      exact hconf_acc s' st hst f hf
    · exact hnodup
    · exact hdisj
  exact StepTrace.recovery_exactness_cor62_fiber_stable ht hstart iterOf hind hiter hn_mem hm_mem
    hnodup hdisj hwithdraw hwithdraw_on hopen hconf_self hself_withdraw hconf_non_self hno_remove
    hno_insert hconf_trace

end StepTrace

end Faithful

end Cordix
