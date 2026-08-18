import LeanCordix.FullCtx
import LeanCordix.Iterator
import LeanCordix.Coeffect

/-!
# LeanCordix.Basic — faithful full-context model, basic layer

Definitions and basic infrastructure of the canonical full-context model:
`Component`, `Lifecycle`, `Fiber`, `Registry`, `State`, the raw/active
sigma operations, registry lemmas, write-confinement interfaces, and
pointwise fiber agreement.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

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
  (s.ambient, rawSigma s.reg)

/-- The coeffect context of a faithful state. -/
def sigmaOf {N : Type} {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) : CoefCtx K V :=
  Cordix.sigmaOf s.reg

/-- The provider map of a faithful state. -/
def providerOf {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (k : K) : Option N :=
  Cordix.providerOf s.reg k

/-- The target view of `n` at a faithful state. -/
noncomputable def targetOf {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} (s : State N K E V) (n : N) : Option (K → Option N) :=
  Cordix.targetOf s.reg n

/-- Quiescence at a faithful state. -/
def quiet {N : Type} [DecidableEq N] {K : Type} [DecidableEq K] {E : Type}
    {V : K → Type u} (s : State N K E V) : Prop :=
  Cordix.quiet s.reg

/-- The withdrawal guard at a faithful state. -/
def relied {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (n : N) : Prop :=
  Cordix.relied s.reg n

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

