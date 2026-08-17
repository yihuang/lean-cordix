import LeanCordix.TraceModel

/-
# Cordix — Lemma 55 support: observational state equivalence

This module defines the observational equivalence relation used by
Lemma 55 (`≃`-invariance).  A lifecycle state is related to another when the
rule-visible fields are equal, with iterators compared by their complete
step functions; a state is related when ambient context, `sigmaOf`,
`providerOf`, `targetOf`, `relied`, name domains, and the rule-visible fiber
fields are all equal.

It also transports steps along `State.Equiv`: if two states are related
then every rule of Section 4.3 that applies at one state applies at the
other, acting on the same name with the same rule kind.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- Two iterators with the same step function are the same iterator. -/
theorem Iterator.eq_of_step_eq {ι ι' : Iterator (CoefCtx K V) E}
    (h : ∀ γ, Cordix.Iterator.step ι γ = Cordix.Iterator.step ι' γ) : ι = ι' := by
  cases ι with
  | mk run =>
  cases ι' with
  | mk run' =>
    congr
    funext γ
    exact h γ

def Lifecycle.Equiv : Lifecycle N K V E → Lifecycle N K V E → Prop
  | .inactive o, .inactive o' => o = o'
  | .loading ι κ v, .loading ι' κ' v' =>
      (∀ γ, Cordix.Iterator.step ι γ = Cordix.Iterator.step ι' γ) ∧ κ = κ' ∧ v = v'
  | .active κ v, .active κ' v' => κ = κ' ∧ v = v'
  | .unloading κ v o, .unloading κ' v' o' => κ = κ' ∧ v = v' ∧ o = o'
  | _, _ => False

namespace Lifecycle.Equiv

theorem installed_iff {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    lc.installed ↔ lc'.installed := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv, Lifecycle.installed] at h ⊢

theorem viewOf_eq {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    lc.viewOf = lc'.viewOf := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv, Lifecycle.viewOf] at h ⊢
  · rcases h with ⟨_, hκ, hv⟩; exact hv
  · rcases h with ⟨hκ, hv⟩; exact hv
  · rcases h with ⟨hκ, hv, _⟩; exact hv

theorem symm {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    Lifecycle.Equiv lc' lc := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv] at h ⊢
  · exact h.symm
  · rcases h with ⟨hstep, hκ, hv⟩
    exact ⟨fun γ => (hstep γ).symm, hκ.symm, hv.symm⟩
  · rcases h with ⟨hκ, hv⟩; exact ⟨hκ.symm, hv.symm⟩
  · rcases h with ⟨hκ, hv, ho⟩; exact ⟨hκ.symm, hv.symm, ho.symm⟩

/-- If an `inactive` lifecycle is related to another, that other is the
same `inactive` outcome. -/
theorem inactive_of_inactive {o : Option E} {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.inactive o) lc') : lc' = .inactive o := by
  cases lc' with
  | inactive o' => simp [Lifecycle.Equiv] at h; rw [← h]
  | loading ι κ v => simp [Lifecycle.Equiv] at h
  | active κ v => simp [Lifecycle.Equiv] at h
  | unloading κ v o' => simp [Lifecycle.Equiv] at h

/-- If a `loading` lifecycle is related to another, the other is a
`loading` with the same accumulator and committed view, and its iterator
has the same step function. -/
theorem loading_of_loading {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.loading ι κ v) lc') :
    ∃ ι', lc' = .loading ι' κ v ∧ ι = ι' := by
  cases lc' with
  | inactive o => simp [Lifecycle.Equiv] at h
  | loading ι' κ' v' =>
      simp [Lifecycle.Equiv] at h
      rcases h with ⟨hstep, hκ, hv⟩
      subst κ'
      subst v'
      exact ⟨ι', rfl, Iterator.eq_of_step_eq hstep⟩
  | active κ' v' => simp [Lifecycle.Equiv] at h
  | unloading κ' v' o' => simp [Lifecycle.Equiv] at h

/-- If an `active` lifecycle is related to another, that other is `active`
with the same accumulator and committed view. -/
theorem active_of_active {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N}
    {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.active κ v) lc') : lc' = .active κ v := by
  cases lc' with
  | inactive o => simp [Lifecycle.Equiv] at h
  | loading ι κ' v' => simp [Lifecycle.Equiv] at h
  | active κ' v' =>
      simp [Lifecycle.Equiv] at h
      rcases h with ⟨hκ, hv⟩
      subst κ'
      subst v'
      rfl
  | unloading κ' v' o' => simp [Lifecycle.Equiv] at h

/-- If an `unloading` lifecycle is related to another, that other is
`unloading` with the same accumulator, committed view, and outcome. -/
theorem unloading_of_unloading {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N}
    {o : Option E} {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.unloading κ v o) lc') : lc' = .unloading κ v o := by
  cases lc' with
  | inactive o' => simp [Lifecycle.Equiv] at h
  | loading ι κ' v' => simp [Lifecycle.Equiv] at h
  | active κ' v' => simp [Lifecycle.Equiv] at h
  | unloading κ' v' o' =>
      simp [Lifecycle.Equiv] at h
      rcases h with ⟨hκ, hv, ho⟩
      subst κ'
      subst v'
      subst o'
      rfl

end Lifecycle.Equiv

/-- The sigma contribution of a fiber: its table when active, otherwise
`none`. -/
def Fiber.sigmaContrib (f : Fiber N K V E) (k : K) : Option (V k) :=
  match f.lc with
  | .active _ _ => f.table k
  | _ => none

/-- The provider contribution of a fiber: whether its table defines `k`
when active. -/
def Fiber.provContrib (f : Fiber N K V E) (k : K) : Bool :=
  match f.lc with
  | .active _ _ => (f.table k).isSome
  | _ => false

/-- The rule-visible fields of a fiber. -/
def Fiber.Equiv (f f' : Fiber N K V E) : Prop :=
  f.comp = f'.comp ∧ f.parent = f'.parent ∧ f.retired = f'.retired ∧
    f.table = f'.table ∧ Lifecycle.Equiv f.lc f'.lc

namespace Fiber.Equiv

theorem comp {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : f.comp = f'.comp := h.1

theorem parent {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : f.parent = f'.parent := h.2.1

theorem retired {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : f.retired = f'.retired := h.2.2.1

theorem table {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : f.table = f'.table := h.2.2.2.1

theorem lc {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : Lifecycle.Equiv f.lc f'.lc := h.2.2.2.2

theorem installed_iff {f f' : Fiber N K V E} (h : Fiber.Equiv f f') :
    f.lc.installed ↔ f'.lc.installed :=
  Lifecycle.Equiv.installed_iff h.lc

theorem viewOf_eq {f f' : Fiber N K V E} (h : Fiber.Equiv f f') :
    f.lc.viewOf = f'.lc.viewOf :=
  Lifecycle.Equiv.viewOf_eq h.lc

theorem symm {f f' : Fiber N K V E} (h : Fiber.Equiv f f') : Fiber.Equiv f' f :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, Lifecycle.Equiv.symm h.2.2.2.2⟩

end Fiber.Equiv

/-- Observational equivalence of states for the rules of Section 4.3. -/
structure State.Equiv (s s' : State N K E V) : Prop where
  nodup : NodupKeys s.reg
  nodup' : NodupKeys s'.reg
  ambient : s.ambient = s'.ambient
  sigmaOf : Full.sigmaOf s.reg = Full.sigmaOf s'.reg
  providerOf : Full.providerOf s.reg = Full.providerOf s'.reg
  targetOf : ∀ n, Full.targetOf s.reg n = Full.targetOf s'.reg n
  relied : ∀ n, Full.relied s.reg n ↔ Full.relied s'.reg n
  domain : ∀ n, (lookup s.reg n).isSome ↔ (lookup s'.reg n).isSome
  fields : ∀ n f f', lookup s.reg n = some f → lookup s'.reg n = some f' →
    Fiber.Equiv f f'

namespace State.Equiv

theorem symm {s s' : State N K E V} (h : State.Equiv s s') : State.Equiv s' s where
  nodup := h.nodup'
  nodup' := h.nodup
  ambient := h.ambient.symm
  sigmaOf := h.sigmaOf.symm
  providerOf := h.providerOf.symm
  targetOf := fun n => (h.targetOf n).symm
  relied := fun n => (h.relied n).symm
  domain := fun n => (h.domain n).symm
  fields := fun n f' f hf' hf => Fiber.Equiv.symm (h.fields n f f' hf hf')

/-- A name present in the first registry is present in the second. -/
theorem lookup_some {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    {f : Fiber N K V E} (hf : lookup s.reg n = some f) :
    ∃ f', lookup s'.reg n = some f' := by
  have hn : (lookup s'.reg n).isSome := (h.domain n).mp (by rw [hf]; simp)
  exact Option.isSome_iff_exists.mp hn

/-- A name present in the second registry is present in the first. -/
theorem lookup_some_symm {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    {f' : Fiber N K V E} (hf' : lookup s'.reg n = some f') :
    ∃ f, lookup s.reg n = some f :=
  h.symm.lookup_some hf'

/-- A name absent from the first registry is absent from the second. -/
theorem lookup_none {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    (hn : lookup s.reg n = none) : lookup s'.reg n = none := by
  by_cases h' : (lookup s'.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h' with ⟨f', hf'⟩
    rcases h.lookup_some_symm hf' with ⟨f, hf⟩
    rw [hn] at hf
    simp at hf
  · exact Option.not_isSome_iff_eq_none.mp h'

/-- A name absent from the second registry is absent from the first. -/
theorem lookup_none_symm {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    (hn : lookup s'.reg n = none) : lookup s.reg n = none :=
  h.symm.lookup_none hn

end State.Equiv

/-! ## Congruence helpers for `targetOf` and `relied` -/

/-- `targetOf` is congruent in `sigmaOf`, `providerOf`, the name domain,
and the rule-visible fiber fields. -/
theorem targetOf_congr {r r' : Registry N K V E}
    (hsig : Full.sigmaOf r = Full.sigmaOf r')
    (hprov : Full.providerOf r = Full.providerOf r')
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    (hfields : ∀ n f f', lookup r n = some f → lookup r' n = some f' →
      Fiber.Equiv f f') :
    ∀ n, Full.targetOf r n = Full.targetOf r' n := by
  classical
  intro n
  cases hlook : lookup r n with
  | none =>
      have hlook' : lookup r' n = none := by
        cases h' : lookup r' n with
        | none => rfl
        | some f' =>
            have : (lookup r n).isSome := (hdom n).2 (by simp [h'])
            rw [hlook] at this
            simp at this
      simp [Full.targetOf, hlook, hlook']
  | some f =>
      rcases Option.isSome_iff_exists.mp ((hdom n).mp (by simp [hlook])) with ⟨f', hf'⟩
      have hff := hfields n f f' hlook hf'
      simp [Full.targetOf, hlook, hf', hff.comp, hff.retired, hsig, hprov]

/-- `relied` is congruent in the name domain and the rule-visible fiber
fields. -/
theorem relied_congr {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    (hfields : ∀ n f f', lookup r n = some f → lookup r' n = some f' →
      Fiber.Equiv f f') :
    ∀ n, Full.relied r n ↔ Full.relied r' n := by
  intro n
  unfold Full.relied
  constructor
  · rintro ⟨n', k, f, hf, hn', hinst, hv⟩
    rcases Option.isSome_iff_exists.mp ((hdom n').mp (by simp [hf])) with ⟨f', hf'⟩
    have hff := hfields n' f f' hf hf'
    refine ⟨n', k, f', hf', hn', (hff.installed_iff).1 hinst, ?_⟩
    rw [← hff.viewOf_eq]
    exact hv
  · rintro ⟨n', k, f', hf', hn', hinst, hv⟩
    rcases Option.isSome_iff_exists.mp ((hdom n').2 (by simp [hf'])) with ⟨f, hf⟩
    have hff := hfields n' f f' hf hf'
    refine ⟨n', k, f, hf, hn', (hff.installed_iff).2 hinst, ?_⟩
    rw [hff.viewOf_eq]
    exact hv

/-! ## Pointwise update and deletion preserve the fiber-wise fields -/

/-- `set` preserves the name domain, pointwise. -/
theorem domain_set {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    {n : N} {g g' : Fiber N K V E} :
    ∀ m, (lookup (set r n g) m).isSome ↔ (lookup (set r' n g') m).isSome := by
  intro m
  by_cases hmn : m = n
  · subst m
    simp [lookup_set_eq]
  · simp [lookup_set_ne r n m g hmn, lookup_set_ne r' n m g' hmn, hdom m]

/-- `set` preserves the rule-visible fiber fields. -/
theorem fields_set {r r' : Registry N K V E}
    (hfields : ∀ m f f', lookup r m = some f → lookup r' m = some f' →
      Fiber.Equiv f f')
    {n : N} {g g' : Fiber N K V E} (hgg : Fiber.Equiv g g') :
    ∀ m h h', lookup (set r n g) m = some h → lookup (set r' n g') m = some h' →
      Fiber.Equiv h h' := by
  intro m h h' hm hm'
  by_cases hmn : m = n
  · subst m
    simp [lookup_set_eq] at hm hm'
    subst h
    subst h'
    exact hgg
  · have hmr : lookup r m = some h := by
      simpa [lookup_set_ne r n m g hmn] using hm
    have hmr' : lookup r' m = some h' := by
      simpa [lookup_set_ne r' n m g' hmn] using hm'
    exact hfields m h h' hmr hmr'

/-- `del` preserves the name domain, pointwise. -/
theorem domain_del {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome) {n : N} :
    ∀ m, (lookup (del r n) m).isSome ↔ (lookup (del r' n) m).isSome := by
  intro m
  by_cases hmn : m = n
  · subst m
    simp [lookup_del_self]
  · simp [lookup_del_ne r n m hmn, lookup_del_ne r' n m hmn, hdom m]

/-- `del` preserves the rule-visible fiber fields. -/
theorem fields_del {r r' : Registry N K V E}
    (hfields : ∀ m f f', lookup r m = some f → lookup r' m = some f' →
      Fiber.Equiv f f')
    {n : N} :
    ∀ m h h', lookup (del r n) m = some h → lookup (del r' n) m = some h' →
      Fiber.Equiv h h' := by
  intro m h h' hm hm'
  have hc := lookup_del_cases (n := n) hm
  rcases hc with ⟨hmn, hmr⟩
  have hc' := lookup_del_cases (n := n) hm'
  rcases hc' with ⟨_, hmr'⟩
  exact hfields m h h' hmr hmr'

/-- Assemble `State.Equiv` from equality of the ambient context and the
registry-level observations. -/
theorem State.Equiv.of_registry {s s' : State N K E V}
    (hn : NodupKeys s.reg) (hn' : NodupKeys s'.reg)
    (hamb : s.ambient = s'.ambient)
    (hsig : Full.sigmaOf s.reg = Full.sigmaOf s'.reg)
    (hprov : Full.providerOf s.reg = Full.providerOf s'.reg)
    (hdom : ∀ n, (lookup s.reg n).isSome ↔ (lookup s'.reg n).isSome)
    (hfields : ∀ n f f', lookup s.reg n = some f → lookup s'.reg n = some f' →
      Fiber.Equiv f f') :
    State.Equiv s s' where
  nodup := hn
  nodup' := hn'
  ambient := hamb
  sigmaOf := hsig
  providerOf := hprov
  targetOf := targetOf_congr hsig hprov hdom hfields
  relied := relied_congr hdom hfields
  domain := hdom
  fields := hfields

/-! ## `set` and `del` preserve `sigmaOf` and `providerOf` -/

/-- If the old and new fibers have the same sigma contribution, then `set`
does not change `sigmaOf`. -/
theorem sigmaOf_set_eq_sigmaOf_of_contrib_eq {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E}
    (hf : lookup r n = some f)
    (hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                (match f.lc with | .active _ _ => f.table k | _ => none)) :
    Full.sigmaOf (set r n g) = Full.sigmaOf r := by
  funext k
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : (match g.lc with | .active _ _ => g.table k | _ => none) =
            (match p.2.lc with | .active _ _ => p.2.table k | _ => none) := by
          simpa [hf_eq] using hcg k
        rw [show Cordix.Full.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.Full.set, hpn]]
        have hcons : Full.sigmaOf ((n, g) :: rest) k = Full.sigmaOf ((n, p.2) :: rest) k := by
          cases hg : g.lc <;> cases hp : p.2.lc <;>
            simp [Full.sigmaOf, List.foldr, hg, hp] at hcg' ⊢
          case inactive.active => rw [← hcg']; rfl
          case loading.active => rw [← hcg']; rfl
          case unloading.active => rw [← hcg']; rfl
          case active.inactive => rw [hcg']; rfl
          case active.loading => rw [hcg']; rfl
          case active.unloading => rw [hcg']; rfl
          case active.active => rw [hcg']
        change Full.sigmaOf ((n, g) :: rest) k = Full.sigmaOf ((p.1, p.2) :: rest) k
        rw [hpn]
        exact hcons
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
          simp [Cordix.Full.set, hpn]]
        exact sigmaOf_cons_congr_k p k (ih hn_rest hf_rest)

/-- Helper for `providerOf_set_eq_providerOf_of_contrib_eq`: equal provider
contributions at the head give equal `providerOf` folds. -/
theorem providerOf_cons_eq_of_contrib_eq {n : N} {g : Fiber N K V E}
    {p : N × Fiber N K V E} (rest : Registry N K V E) {k : K}
    (hcg : (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
           (match p.2.lc with | .active _ _ => (p.2.table k).isSome | _ => False)) :
    Full.providerOf ((n, g) :: rest) k = Full.providerOf ((n, p.2) :: rest) k := by
  cases hg : g.lc <;> cases hp : p.2.lc <;>
    simp [Full.providerOf, List.foldr, hg, hp] at hcg ⊢
  case inactive.active => simp [hcg]
  case loading.active => simp [hcg]
  case unloading.active => simp [hcg]
  case active.inactive => simp [hcg]
  case active.loading => simp [hcg]
  case active.unloading => simp [hcg]
  case active.active => simp [hcg]

/-- If the old and new fibers have the same provider contribution, then
`set` does not change `providerOf`. -/
theorem providerOf_set_eq_providerOf_of_contrib_eq {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E}
    (hf : lookup r n = some f)
    (hcg : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                (match f.lc with | .active _ _ => (f.table k).isSome | _ => False)) :
    Full.providerOf (set r n g) = Full.providerOf r := by
  funext k
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
            (match p.2.lc with | .active _ _ => (p.2.table k).isSome | _ => False) := by
          simpa [hf_eq] using hcg k
        rw [show Cordix.Full.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.Full.set, hpn]]
        change Full.providerOf ((n, g) :: rest) k = Full.providerOf ((p.1, p.2) :: rest) k
        rw [hpn]
        exact providerOf_cons_eq_of_contrib_eq rest hcg'
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
          simp [Cordix.Full.set, hpn]]
        exact providerOf_cons_congr_k p k (ih hn_rest hf_rest)

/-- Inserting a fresh inactive fiber does not change `sigmaOf`. -/
theorem sigmaOf_set_fresh_eq {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    (hn : lookup r n = none)
    (hno : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) = none) :
    Full.sigmaOf (set r n g) = Full.sigmaOf r := by
  funext k
  induction r with
  | nil =>
      cases hg : g.lc <;> simp [Cordix.Full.set, Full.sigmaOf, List.foldr, hg]
      case active => simpa [hg] using hno k
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        have : lookup (p :: rest) n = some p.2 := by simp [lookup, hEq]
        rw [hn] at this
        simp at this
      have hn_rest : lookup rest n = none := by
        simpa [lookup, hpn] using hn
      rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
        simp [Cordix.Full.set, hpn]]
      exact sigmaOf_cons_congr_k p k (ih hn_rest)

/-- Inserting a fresh inactive fiber does not change `providerOf`. -/
theorem providerOf_set_fresh_eq {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    (hn : lookup r n = none)
    (hno : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) = False) :
    Full.providerOf (set r n g) = Full.providerOf r := by
  funext k
  induction r with
  | nil =>
      cases hg : g.lc <;> simp [Cordix.Full.set, Full.providerOf, List.foldr, hg]
      case active => simpa [hg] using hno k
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        have : lookup (p :: rest) n = some p.2 := by simp [lookup, hEq]
        rw [hn] at this
        simp at this
      have hn_rest : lookup rest n = none := by
        simpa [lookup, hpn] using hn
      rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
        simp [Cordix.Full.set, hpn]]
      exact providerOf_cons_congr_k p k (ih hn_rest)

/-- A pointwise update that preserves the sigma/provider contribution of
the acting fiber preserves `State.Equiv`. -/
theorem State.Equiv.set {s s' : State N K E V} (h : State.Equiv s s')
    {n : N} {f f' g g' : Fiber N K V E}
    (hf : lookup s.reg n = some f) (hf' : lookup s'.reg n = some f')
    (hgg : Fiber.Equiv g g')
    (hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                (match f.lc with | .active _ _ => f.table k | _ => none))
    (hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                 (match f'.lc with | .active _ _ => f'.table k | _ => none))
    (hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                  (match f.lc with | .active _ _ => (f.table k).isSome | _ => False))
    (hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                   (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False)) :
    State.Equiv ⟨Cordix.Full.set s.reg n g, s.ambient⟩
      ⟨Cordix.Full.set s'.reg n g', s'.ambient⟩ := by
  apply State.Equiv.of_registry
  · exact nodupKeys_set s.reg n g h.nodup
  · exact nodupKeys_set s'.reg n g' h.nodup'
  · exact h.ambient
  · calc
      Full.sigmaOf (Cordix.Full.set s.reg n g) = Full.sigmaOf s.reg :=
        sigmaOf_set_eq_sigmaOf_of_contrib_eq h.nodup hf hcg
      _ = Full.sigmaOf s'.reg := h.sigmaOf
      _ = Full.sigmaOf (Cordix.Full.set s'.reg n g') :=
        (sigmaOf_set_eq_sigmaOf_of_contrib_eq h.nodup' hf' hcg').symm
  · calc
      Full.providerOf (Cordix.Full.set s.reg n g) = Full.providerOf s.reg :=
        providerOf_set_eq_providerOf_of_contrib_eq h.nodup hf hprov
      _ = Full.providerOf s'.reg := h.providerOf
      _ = Full.providerOf (Cordix.Full.set s'.reg n g') :=
        (providerOf_set_eq_providerOf_of_contrib_eq h.nodup' hf' hprov').symm
  · exact domain_set h.domain
  · exact fields_set h.fields hgg

/-- Inserting a fresh inactive fiber at the same absent name in both states
preserves `State.Equiv`. -/
theorem State.Equiv.fresh_set {s s' : State N K E V} (h : State.Equiv s s')
    {n : N} {g g' : Fiber N K V E}
    (hn : lookup s.reg n = none) (hn' : lookup s'.reg n = none)
    (hgg : Fiber.Equiv g g')
    (hno : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) = none)
    (hno' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) = none)
    (hnoP : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) = False)
    (hnoP' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) = False) :
    State.Equiv ⟨Cordix.Full.set s.reg n g, s.ambient⟩
      ⟨Cordix.Full.set s'.reg n g', s'.ambient⟩ := by
  apply State.Equiv.of_registry
  · exact nodupKeys_set s.reg n g h.nodup
  · exact nodupKeys_set s'.reg n g' h.nodup'
  · exact h.ambient
  · calc
      Full.sigmaOf (Cordix.Full.set s.reg n g) = Full.sigmaOf s.reg :=
        sigmaOf_set_fresh_eq hn hno
      _ = Full.sigmaOf s'.reg := h.sigmaOf
      _ = Full.sigmaOf (Cordix.Full.set s'.reg n g') :=
        (sigmaOf_set_fresh_eq hn' hno').symm
  · calc
      Full.providerOf (Cordix.Full.set s.reg n g) = Full.providerOf s.reg :=
        providerOf_set_fresh_eq hn hnoP
      _ = Full.providerOf s'.reg := h.providerOf
      _ = Full.providerOf (Cordix.Full.set s'.reg n g') :=
        (providerOf_set_fresh_eq hn' hnoP').symm
  · exact domain_set h.domain
  · exact fields_set h.fields hgg

/-- In a duplicate-free registry, if the unique entry at `n` is inactive,
then every entry at `n` is inactive. -/
theorem all_inactive_of_lookup_inactive {r : Registry N K V E} (hn : NodupKeys r)
    {n : N} {f : Fiber N K V E} {o : Option E}
    (hf : lookup r n = some f) (hl : f.lc = .inactive o) :
    ∀ p ∈ r, p.1 = n → ∃ o', p.2.lc = .inactive o' := by
  induction r with
  | nil => intro p hp; simp at hp
  | cons q rest ih =>
      intro p hp hpn
      have hn_rest : NodupKeys rest := by
        change ((q.1 :: rest.map (fun x => x.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        exact hn.2
      by_cases hq : q.1 = n
      · have hfq : lookup (q :: rest) n = some q.2 := by simp [lookup, hq]
        have hf_eq : f = q.2 := Option.some.inj (hf.symm.trans hfq)
        cases p with
        | mk a b =>
            simp at hp
            rcases hp with hEq | hmem
            · cases hEq
              exact ⟨o, by rwa [← hf_eq]⟩
            · exfalso
              have haq : a = q.1 := by simpa [hpn, hq]
              have hqmem : q.1 ∈ rest.map (fun x => x.1) := by
                rw [List.mem_map]
                exact ⟨(a, b), hmem, haq⟩
              exact (List.nodup_cons.mp hn).1 hqmem
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hq] using hf
        cases p with
        | mk a b =>
            simp at hp
            rcases hp with hEq | hmem
            · exfalso
              apply hq
              cases hEq
              exact hpn
            · exact ih hn_rest hf_rest (a, b) hmem hpn

/-- Under well-formedness and the table-provision invariant, two fibers
whose tables both define the same key must be the same fiber. -/
theorem tableProv_unique_provider {r : Registry N K V E}
    (hwf : WellFormed r) (htp : TableProv r) {k : K}
    {n f n' f' : _} (hf : lookup r n = some f) (hf' : lookup r n' = some f')
    (ht : (f.table k).isSome) (ht' : (f'.table k).isSome) : n = n' := by
  by_cases hne : n = n'
  · exact hne
  · exfalso
    have hk : k ∈ f.comp.prov := htp n f hf k ht
    have hk' : k ∈ f'.comp.prov := htp n' f' hf' k ht'
    exact hwf.provDisj n f n' f' hf hf' hne k hk k hk' rfl

/-- A member of a duplicate-free registry is found by `lookup`. -/
theorem lookup_self_of_mem_of_nodup {r : Registry N K V E} (hn : NodupKeys r)
    {p : N × Fiber N K V E} (hp : p ∈ r) : lookup r p.1 = some p.2 := by
  induction r with
  | nil => simp at hp
  | cons q rest ih =>
      have hn_rest : NodupKeys rest := by
        change ((q.1 :: rest.map (fun x => x.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        exact hn.2
      simp at hp
      rcases hp with hEq | hmem
      · cases hEq
        simp [lookup]
      · have hne : q.1 ≠ p.1 := by
          intro heq
          have : q.1 ∈ rest.map (fun x => x.1) := by
            rw [List.mem_map]
            exact ⟨p, hmem, heq.symm⟩
          exact (List.nodup_cons.mp hn).1 this
        simp [lookup, hne, ih hn_rest hmem]

/-- If no fiber contributes to `sigmaOf` at `k`, then `sigmaOf r k` is
`none`. -/
theorem sigmaOf_eq_none_of_no_sigma {r : Registry N K V E} {k : K}
    (h : ∀ p ∈ r, Fiber.sigmaContrib p.2 k = none) :
    Full.sigmaOf r k = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      have hp := h p (by simp)
      have hrest : ∀ q ∈ rest, Fiber.sigmaContrib q.2 k = none := by
        intro q hq; exact h q (by simp [hq])
      cases hlc : p.2.lc with
      | inactive o => simpa [Full.sigmaOf, List.foldr, hlc] using ih hrest
      | loading ι κ v => simpa [Full.sigmaOf, List.foldr, hlc] using ih hrest
      | active κ v =>
          have hp' : p.2.table k = none := by
            simpa [Fiber.sigmaContrib, hlc] using hp
          simpa [Full.sigmaOf, List.foldr, hlc, hp'] using ih hrest
      | unloading κ v o => simpa [Full.sigmaOf, List.foldr, hlc] using ih hrest

/-- If no fiber contributes to `providerOf` at `k`, then `providerOf r k`
is `none`. -/
theorem providerOf_eq_none_of_no_prov {r : Registry N K V E} {k : K}
    (h : ∀ p ∈ r, Fiber.provContrib p.2 k = false) :
    Full.providerOf r k = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      have hp := h p (by simp)
      have hrest : ∀ q ∈ rest, Fiber.provContrib q.2 k = false := by
        intro q hq; exact h q (by simp [hq])
      cases hlc : p.2.lc with
      | inactive o => simpa [Full.providerOf, List.foldr, hlc] using ih hrest
      | loading ι κ v => simpa [Full.providerOf, List.foldr, hlc] using ih hrest
      | active κ v =>
          have hp' : (p.2.table k).isSome = false := by
            simpa [Fiber.provContrib, hlc] using hp
          simpa [Full.providerOf, List.foldr, hlc, hp'] using ih hrest
      | unloading κ v o => simpa [Full.providerOf, List.foldr, hlc] using ih hrest

/-- If a fiber has a non-`none` sigma contribution, then its provider
contribution is `true`. -/
theorem Fiber.provContrib_eq_true_of_sigmaContrib_ne_none {f : Fiber N K V E} {k : K}
    (h : ¬ Fiber.sigmaContrib f k = none) : Fiber.provContrib f k = true := by
  cases hlc : f.lc with
  | active κ v =>
      simp [Fiber.sigmaContrib, Fiber.provContrib, hlc] at h ⊢
      cases ht : f.table k with
      | none => simp [Fiber.sigmaContrib, ht] at h
      | some x => simp [Fiber.provContrib, hlc, ht]
  | inactive o => simp [Fiber.sigmaContrib, Fiber.provContrib, hlc] at h
  | loading ι κ v => simp [Fiber.sigmaContrib, Fiber.provContrib, hlc] at h
  | unloading κ v o => simp [Fiber.sigmaContrib, Fiber.provContrib, hlc] at h

/-- If the provider contribution is `true`, then the table defines the
key. -/
theorem Fiber.table_isSome_of_provContrib_eq_true {f : Fiber N K V E} {k : K}
    (h : Fiber.provContrib f k = true) : (f.table k).isSome := by
  cases hlc : f.lc with
  | active κ v => simp [Fiber.provContrib, hlc] at h; exact h
  | inactive o => simp [Fiber.provContrib, hlc] at h
  | loading ι κ v => simp [Fiber.provContrib, hlc] at h
  | unloading κ v o => simp [Fiber.provContrib, hlc] at h

/-- A member of `set r n g` whose name is not `n` is already a member of
`r`. -/
theorem mem_set_of_ne {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    {q : N × Fiber N K V E} (hq : q ∈ Cordix.Full.set r n g) (hqn : q.1 ≠ n) :
    q ∈ r := by
  induction r with
  | nil =>
      simp [Cordix.Full.set] at hq
      have hq1 : q.1 = n := by simpa [hq]
      exact absurd hq1 hqn
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · simp [Cordix.Full.set, hpn] at hq
        rcases hq with hEq | hmem
        · have hq1 : q.1 = n := by simpa [hEq]
          exact absurd hq1 hqn
        · exact List.Mem.tail _ hmem
      · simp [Cordix.Full.set, hpn] at hq
        rcases hq with hEq | hmem
        · rw [hEq]
          exact List.Mem.head _
        · exact List.Mem.tail _ (ih hmem)

/-- If the unique active provider of `k` at `n` is unloaded, then `k` has
no provider left. -/
theorem providerOf_set_unloading_eq_none {r : Registry N K V E} (hn : NodupKeys r)
    (hwf : WellFormed r) (htp : TableProv r) {n : N} {f : Fiber N K V E}
    {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N}
    (hf : lookup r n = some f) (hl : f.lc = .active κ v) {k : K}
    (ht : (f.table k).isSome) :
    Full.providerOf (Cordix.Full.set r n { f with lc := .unloading κ v none }) k = none := by
  apply providerOf_eq_none_of_no_prov
  intro q hq
  by_cases hqn : q.1 = n
  · have hq_lookup : lookup (Cordix.Full.set r n { f with lc := .unloading κ v none }) q.1 = some q.2 :=
      lookup_self_of_mem_of_nodup (nodupKeys_set r n { f with lc := .unloading κ v none } hn) hq
    rw [hqn] at hq_lookup
    have hq_eq : q.2 = { f with lc := .unloading κ v none } := by
      rw [lookup_set_eq] at hq_lookup
      exact Option.some.inj hq_lookup.symm
    simp [Fiber.provContrib, hq_eq]
  · have hq_in_r : q ∈ r := mem_set_of_ne hq hqn
    by_cases hsome : Fiber.provContrib q.2 k = true
    · exfalso
      have hq_lookup : lookup r q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome := Fiber.table_isSome_of_provContrib_eq_true hsome
      have huniq := tableProv_unique_provider hwf htp hf hq_lookup ht hq_table
      exact hqn huniq.symm
    · cases hb : Fiber.provContrib q.2 k <;> simp [hb] at hsome ⊢

/-- If the unique active table provider of `k` at `n` is unloaded, then
`k` disappears from `sigmaOf`. -/
theorem sigmaOf_set_unloading_eq_none {r : Registry N K V E} (hn : NodupKeys r)
    (hwf : WellFormed r) (htp : TableProv r) {n : N} {f : Fiber N K V E}
    {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N}
    (hf : lookup r n = some f) (hl : f.lc = .active κ v) {k : K}
    (ht : (f.table k).isSome) :
    Full.sigmaOf (Cordix.Full.set r n { f with lc := .unloading κ v none }) k = none := by
  apply sigmaOf_eq_none_of_no_sigma
  intro q hq
  by_cases hqn : q.1 = n
  · have hq_lookup : lookup (Cordix.Full.set r n { f with lc := .unloading κ v none }) q.1 = some q.2 :=
      lookup_self_of_mem_of_nodup (nodupKeys_set r n { f with lc := .unloading κ v none } hn) hq
    rw [hqn] at hq_lookup
    have hq_eq : q.2 = { f with lc := .unloading κ v none } := by
      rw [lookup_set_eq] at hq_lookup
      exact Option.some.inj hq_lookup.symm
    simp [Fiber.sigmaContrib, hq_eq]
  · have hq_in_r : q ∈ r := mem_set_of_ne hq hqn
    by_cases hsome : Fiber.sigmaContrib q.2 k = none
    · exact hsome
    · exfalso
      have hq_lookup : lookup r q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome :=
        Fiber.table_isSome_of_provContrib_eq_true
          (Fiber.provContrib_eq_true_of_sigmaContrib_ne_none hsome)
      have huniq := tableProv_unique_provider hwf htp hf hq_lookup ht hq_table
      exact hqn huniq.symm

/-- A table-confined iteration that yields `δ` puts every key `δ` defines
into the component's provision. -/
theorem Component.TableConfined.delta_prov {c : Component K V E}
    {ι : Iterator (CoefCtx K V) E} {δ : CoefCtx K V}
    {hinv : CoefCtx K V → CoefCtx K V}
    {c' : Option (Iterator (CoefCtx K V) E)} {σ : CoefCtx K V}
    (hconf : Component.TableConfined c)
    (hreach : Iterator.Reachable c.iter ι)
    (hstep : Iterator.step ι σ = .ok (δ, hinv, c')) {k : K}
    (ht : (δ k).isSome) : k ∈ c.prov := by
  have hstepconf := hconf hreach
  have h2 := hstepconf.2 σ (fun _ => none)
  rw [hstep] at h2
  have hk := h2 k ht
  cases hk with
  | inl hnone => exact absurd hnone (by simp)
  | inr hprov => exact hprov

/-- `sigmaOf` of a cons is the head's sigma contribution or the tail's. -/
theorem sigmaOf_cons_eq_of_sigmaContrib {p : N × Fiber N K V E}
    {rest : Registry N K V E} {k : K} :
    Full.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Full.sigmaOf rest k) := by
  cases hlc : p.2.lc <;> simp [Full.sigmaOf, List.foldr, Fiber.sigmaContrib, hlc]

/-- `providerOf` of a cons is the head's provider contribution, or the
tail's. -/
theorem providerOf_cons_eq_of_provContrib {p : N × Fiber N K V E}
    {rest : Registry N K V E} {k : K} :
    Full.providerOf (p :: rest) k =
      if Fiber.provContrib p.2 k = true then some p.1 else Full.providerOf rest k := by
  cases hlc : p.2.lc <;> simp [Full.providerOf, List.foldr, Fiber.provContrib, hlc]

/-- `set` preserves `sigmaOf` at a single key when the old and new fibers
have the same sigma contribution there. -/
theorem sigmaOf_set_eq_of_sigmaContrib_eq_k {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E} {k : K}
    (hf : lookup r n = some f)
    (hcg : Fiber.sigmaContrib g k = Fiber.sigmaContrib f k) :
    Full.sigmaOf (Cordix.Full.set r n g) k = Full.sigmaOf r k := by
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : Fiber.sigmaContrib g k = Fiber.sigmaContrib p.2 k := by
          simpa [hf_eq] using hcg
        rw [show Cordix.Full.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.Full.set, hpn]]
        rw [sigmaOf_cons_eq_of_sigmaContrib]
        rw [show Full.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Full.sigmaOf rest k) by
          rw [sigmaOf_cons_eq_of_sigmaContrib]]
        rw [hcg']
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
          simp [Cordix.Full.set, hpn]]
        rw [sigmaOf_cons_eq_of_sigmaContrib]
        rw [show Full.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Full.sigmaOf rest k) by
          rw [sigmaOf_cons_eq_of_sigmaContrib]]
        rw [ih hn_rest hf_rest]

/-- `set` preserves `providerOf` at a single key when the old and new
fibers have the same provider contribution there. -/
theorem providerOf_set_eq_of_provContrib_eq_k {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E} {k : K}
    (hf : lookup r n = some f)
    (hcg : Fiber.provContrib g k = Fiber.provContrib f k) :
    Full.providerOf (Cordix.Full.set r n g) k = Full.providerOf r k := by
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : Fiber.provContrib g k = Fiber.provContrib p.2 k := by
          simpa [hf_eq] using hcg
        rw [show Cordix.Full.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.Full.set, hpn]]
        rw [providerOf_cons_eq_of_provContrib]
        rw [show Full.providerOf (p :: rest) k = if Fiber.provContrib p.2 k = true then some p.1
          else Full.providerOf rest k by
          rw [providerOf_cons_eq_of_provContrib]]
        rw [hcg']
        simp [hpn]
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.Full.set (p :: rest) n g = p :: Cordix.Full.set rest n g by
          simp [Cordix.Full.set, hpn]]
        rw [providerOf_cons_eq_of_provContrib]
        rw [show Full.providerOf (p :: rest) k = if Fiber.provContrib p.2 k = true then some p.1
          else Full.providerOf rest k by
          rw [providerOf_cons_eq_of_provContrib]]
        rw [ih hn_rest hf_rest]

/-- If one entry contributes `some x` at `k` and all other entries
contribute nothing, then `sigmaOf` is `some x`. -/
theorem sigmaOf_eq_some_of_single {r : Registry N K V E} {k : K} {n : N}
    {g : Fiber N K V E} {x : V k}
    (hnodup : NodupKeys r)
    (hg : Fiber.sigmaContrib g k = some x)
    (hother : ∀ q ∈ r, q.1 ≠ n → Fiber.sigmaContrib q.2 k = none)
    (hmem : (n, g) ∈ r) : Full.sigmaOf r k = some x := by
  induction r with
  | nil => simp at hmem
  | cons p rest ih =>
      have hother_rest : ∀ q ∈ rest, q.1 ≠ n → Fiber.sigmaContrib q.2 k = none := by
        intro q hq hqn; exact hother q (by simp [hq]) hqn
      by_cases hpn : p.1 = n
      · have hp_eq : p.2 = g := by
          have hmem' : (n, g) ∈ p :: rest := hmem
          simp at hmem'
          rcases hmem' with hEq | hmemR
          · cases hEq; rfl
          · exfalso
            have hnmem : n ∈ rest.map (fun x => x.1) := by
              rw [List.mem_map]
              exact ⟨(n, g), hmemR, rfl⟩
            exact (List.nodup_cons.mp hnodup).1 (by simpa [hpn] using hnmem)
        have hrest_none : ∀ q ∈ rest, Fiber.sigmaContrib q.2 k = none := by
          intro q hq
          have hq_ne : q.1 ≠ n := by
            intro hEq
            have hnmem : n ∈ rest.map (fun x => x.1) := by
              rw [List.mem_map]
              exact ⟨q, hq, hEq⟩
            exact (List.nodup_cons.mp hnodup).1 (by simpa [hpn] using hnmem)
          exact hother q (by simp [hq]) hq_ne
        have hrest : Full.sigmaOf rest k = none := sigmaOf_eq_none_of_no_sigma hrest_none
        rw [← hp_eq] at hg
        rw [sigmaOf_cons_eq_of_sigmaContrib]
        rw [hg, hrest]
        simp
      · have hp_none : Fiber.sigmaContrib p.2 k = none := hother p (by simp) hpn
        have hnodup_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hnodup
          rw [List.nodup_cons] at hnodup
          exact hnodup.2
        have hmem_rest : (n, g) ∈ rest := by
          have hmem' : (n, g) ∈ p :: rest := hmem
          simp at hmem'
          rcases hmem' with hEq | hmemR
          · exfalso
            have hEq' : p.fst = n := by simpa [← hEq]
            exact hpn hEq'
          · exact hmemR
        have ih' := ih hnodup_rest hother_rest hmem_rest
        rw [sigmaOf_cons_eq_of_sigmaContrib, hp_none]
        exact ih'

/-- If one entry provides `n` at `k` and all other entries provide nothing,
then `providerOf` is `some n`. -/
theorem providerOf_eq_some_of_single {r : Registry N K V E} {k : K} {n : N}
    {g : Fiber N K V E}
    (hnodup : NodupKeys r)
    (hg : Fiber.provContrib g k = true)
    (hother : ∀ q ∈ r, q.1 ≠ n → Fiber.provContrib q.2 k = false)
    (hmem : (n, g) ∈ r) : Full.providerOf r k = some n := by
  induction r with
  | nil => simp at hmem
  | cons p rest ih =>
      have hother_rest : ∀ q ∈ rest, q.1 ≠ n → Fiber.provContrib q.2 k = false := by
        intro q hq hqn; exact hother q (by simp [hq]) hqn
      by_cases hpn : p.1 = n
      · have hp_eq : p.2 = g := by
          have hmem' : (n, g) ∈ p :: rest := hmem
          simp at hmem'
          rcases hmem' with hEq | hmemR
          · cases hEq; rfl
          · exfalso
            have hnmem : n ∈ rest.map (fun x => x.1) := by
              rw [List.mem_map]
              exact ⟨(n, g), hmemR, rfl⟩
            exact (List.nodup_cons.mp hnodup).1 (by simpa [hpn] using hnmem)
        have hrest_none : ∀ q ∈ rest, Fiber.provContrib q.2 k = false := by
          intro q hq
          have hq_ne : q.1 ≠ n := by
            intro hEq
            have hnmem : n ∈ rest.map (fun x => x.1) := by
              rw [List.mem_map]
              exact ⟨q, hq, hEq⟩
            exact (List.nodup_cons.mp hnodup).1 (by simpa [hpn] using hnmem)
          exact hother q (by simp [hq]) hq_ne
        have hrest : Full.providerOf rest k = none := providerOf_eq_none_of_no_prov hrest_none
        rw [← hp_eq] at hg
        rw [providerOf_cons_eq_of_provContrib]
        rw [hg, hrest]
        simp [hpn]
      · have hp_none : Fiber.provContrib p.2 k = false := hother p (by simp) hpn
        have hnodup_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hnodup
          rw [List.nodup_cons] at hnodup
          exact hnodup.2
        have hmem_rest : (n, g) ∈ rest := by
          have hmem' : (n, g) ∈ p :: rest := hmem
          simp at hmem'
          rcases hmem' with hEq | hmemR
          · exfalso
            have hEq' : p.fst = n := by simpa [← hEq]
            exact hpn hEq'
          · exact hmemR
        have ih' := ih hnodup_rest hother_rest hmem_rest
        rw [providerOf_cons_eq_of_provContrib, hp_none]
        exact ih'

/-- `L-Finish` with a non-empty `δ` puts exactly `δ k` into `sigmaOf`. -/
theorem sigmaOf_set_active_eq_of_delta_some {r : Registry N K V E}
    {n : N} {f : Fiber N K V E}
    (hn : NodupKeys r) (hwf : WellFormed r) (htp : TableProv r)
    (hconf : Component.TableConfined f.comp)
    {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {δ : CoefCtx K V}
    {hinv : CoefCtx K V → CoefCtx K V}
    {c : Option (Iterator (CoefCtx K V) E)}
    (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hstep : Iterator.step ι (Full.sigmaOf r) = .ok (δ, hinv, c)) {k : K}
    (ht : (δ k).isSome) :
    Full.sigmaOf (Cordix.Full.set r n { f with table := δ, lc := .active (κ ∘ hinv) v }) k = δ k := by
  let new : Fiber N K V E := { f with table := δ, lc := .active (κ ∘ hinv) v }
  rcases Option.isSome_iff_exists.mp ht with ⟨x, hx⟩
  have hnew_sigma : Fiber.sigmaContrib new k = some x := by
    simp [Fiber.sigmaContrib, new, hx]
  have hmem : (n, new) ∈ Cordix.Full.set r n new := by
    exact lookup_some_mem (lookup_set_eq r n new)
  have hother : ∀ q ∈ Cordix.Full.set r n new, q.1 ≠ n → Fiber.sigmaContrib q.2 k = none := by
    intro q hq hqn
    by_cases hsome : Fiber.sigmaContrib q.2 k = none
    · exact hsome
    · exfalso
      have hq_in_r : q ∈ r := mem_set_of_ne hq hqn
      have hq_lookup : lookup r q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome :=
        Fiber.table_isSome_of_provContrib_eq_true
          (Fiber.provContrib_eq_true_of_sigmaContrib_ne_none hsome)
      have hk_prov : k ∈ f.comp.prov := hconf.delta_prov hreach hstep ht
      have hq_prov : k ∈ q.2.comp.prov := htp q.1 q.2 hq_lookup k hq_table
      exact hwf.provDisj n f q.1 q.2 hf hq_lookup (by intro hEq; exact hqn hEq.symm)
        k hk_prov k hq_prov rfl
  have hnodup_set : NodupKeys (Cordix.Full.set r n new) := nodupKeys_set r n new hn
  change Full.sigmaOf (Cordix.Full.set r n new) k = δ k
  rw [hx]
  exact sigmaOf_eq_some_of_single hnodup_set hnew_sigma hother hmem

/-- `L-Finish` with a non-empty `δ` makes `n` the provider of `k`. -/
theorem providerOf_set_active_eq_of_delta_some {r : Registry N K V E}
    {n : N} {f : Fiber N K V E}
    (hn : NodupKeys r) (hwf : WellFormed r) (htp : TableProv r)
    (hconf : Component.TableConfined f.comp)
    {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {δ : CoefCtx K V}
    {hinv : CoefCtx K V → CoefCtx K V}
    {c : Option (Iterator (CoefCtx K V) E)}
    (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v)
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hstep : Iterator.step ι (Full.sigmaOf r) = .ok (δ, hinv, c)) {k : K}
    (ht : (δ k).isSome) :
    Full.providerOf (Cordix.Full.set r n { f with table := δ, lc := .active (κ ∘ hinv) v }) k = some n := by
  let new : Fiber N K V E := { f with table := δ, lc := .active (κ ∘ hinv) v }
  have hnew_prov : Fiber.provContrib new k = true := by
    simp [Fiber.provContrib, new, ht]
  have hmem : (n, new) ∈ Cordix.Full.set r n new := by
    exact lookup_some_mem (lookup_set_eq r n new)
  have hother : ∀ q ∈ Cordix.Full.set r n new, q.1 ≠ n → Fiber.provContrib q.2 k = false := by
    intro q hq hqn
    by_cases hsome : Fiber.provContrib q.2 k = true
    · exfalso
      have hq_in_r : q ∈ r := mem_set_of_ne hq hqn
      have hq_lookup : lookup r q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome := Fiber.table_isSome_of_provContrib_eq_true hsome
      have hk_prov : k ∈ f.comp.prov := hconf.delta_prov hreach hstep ht
      have hq_prov : k ∈ q.2.comp.prov := htp q.1 q.2 hq_lookup k hq_table
      exact hwf.provDisj n f q.1 q.2 hf hq_lookup (by intro hEq; exact hqn hEq.symm)
        k hk_prov k hq_prov rfl
    · cases hb : Fiber.provContrib q.2 k <;> simp [hb] at hsome ⊢
  have hnodup_set : NodupKeys (Cordix.Full.set r n new) := nodupKeys_set r n new hn
  exact providerOf_eq_some_of_single hnodup_set hnew_prov hother hmem

/-- `L-Finish` with an empty `δ k` leaves `sigmaOf` unchanged at `k`. -/
theorem sigmaOf_set_active_eq_sigmaOf_of_delta_none {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f : Fiber N K V E}
    {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {δ : CoefCtx K V}
    {hinv : CoefCtx K V → CoefCtx K V}
    (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v) {k : K}
    (ht : δ k = none) :
    Full.sigmaOf (Cordix.Full.set r n { f with table := δ, lc := .active (κ ∘ hinv) v }) k =
      Full.sigmaOf r k := by
  let new : Fiber N K V E := { f with table := δ, lc := .active (κ ∘ hinv) v }
  have hcg : Fiber.sigmaContrib new k = Fiber.sigmaContrib f k := by
    simp [Fiber.sigmaContrib, new, hl, ht]
  exact sigmaOf_set_eq_of_sigmaContrib_eq_k hn hf hcg

/-- `L-Finish` with an empty `δ k` leaves `providerOf` unchanged at `k`. -/
theorem providerOf_set_active_eq_sigmaOf_of_delta_none {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f : Fiber N K V E}
    {ι : Iterator (CoefCtx K V) E} {κ : CoefCtx K V → CoefCtx K V}
    {v : K → Option N} {δ : CoefCtx K V}
    {hinv : CoefCtx K V → CoefCtx K V}
    (hf : lookup r n = some f) (hl : f.lc = .loading ι κ v) {k : K}
    (ht : δ k = none) :
    Full.providerOf (Cordix.Full.set r n { f with table := δ, lc := .active (κ ∘ hinv) v }) k =
      Full.providerOf r k := by
  let new : Fiber N K V E := { f with table := δ, lc := .active (κ ∘ hinv) v }
  have hcg : Fiber.provContrib new k = Fiber.provContrib f k := by
    simp [Fiber.provContrib, new, hl, ht]
  exact providerOf_set_eq_of_provContrib_eq_k hn hf hcg

/-! ## Step transport along `State.Equiv` -/

/-- **Lemma 55, applicability half.**  If two states are observationally
equivalent, then every step of the trace-indexed calculus transports to the
other state: there is a step there with the same acting name and rule kind. -/
theorem step_transport {s s' : State N K E V} (h : State.Equiv s s')
    (st : Step s) : ∃ st' : Step s', st'.name = st.name ∧ st'.kind = st.kind := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      have hn' : lookup s'.reg n = none := h.lookup_none hn
      have hp' : ∀ n' ∈ p, ∃ f', lookup s'.reg n' = some f' := by
        intro n' hn'p
        rcases hp n' hn'p with ⟨f, hf⟩
        exact h.lookup_some hf
      have hdisj' : ∀ n' f', lookup s'.reg n' = some f' →
          (∀ k ∈ c.prov, ∀ k' ∈ f'.comp.prov, k ≠ k') := by
        intro n' f' hf'
        rcases h.lookup_some_symm hf' with ⟨f, hf⟩
        have hff := h.fields n' f f' hf hf'
        have hd := hdisj n' f hf
        rw [hff.comp] at hd
        exact hd
      exact ⟨Step.oInsert (s := s') n c p hn' hp' hdisj', rfl, rfl⟩
  | oRetire n f hf =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      exact ⟨Step.oRetire (s := s') n f' hf', rfl, rfl⟩
  | oRemove n f o hf hl hchild =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .inactive o := by
        have hlc : Lifecycle.Equiv (.inactive o) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.inactive_of_inactive hlc
      have hchild' : ∀ n' f', lookup s'.reg n' = some f' → f'.parent ≠ some n := by
        intro n' f' hf'
        rcases h.lookup_some_symm hf' with ⟨f₀, hf₀⟩
        have hff' := h.fields n' f₀ f' hf₀ hf'
        rw [← hff'.parent]
        exact hchild n' f₀ hf₀
      exact ⟨Step.oRemove (s := s') n f' o hf' hl' hchild', rfl, rfl⟩
  | lBegin n f v hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .inactive none := by
        have hlc : Lifecycle.Equiv (.inactive none) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.inactive_of_inactive hlc
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      exact ⟨Step.lBegin (s := s') n f' v hf' hl' ht', rfl, rfl⟩
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, some ι') := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      exact ⟨Step.lIter (s := s') n f' ι₀ κ v ι' δ hinv hreach' hf' hl' ht' hstep', rfl, rfl⟩
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, none) := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      exact ⟨Step.lFinish (s := s') n f' ι₀ κ v δ hinv hreach' hf' hl' ht' hstep', rfl, rfl⟩
  | lRaise n f ι κ v e hreach hf hl hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) = .error e := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      exact ⟨Step.lRaise (s := s') n f' ι₀ κ v e hreach' hf' hl' hstep', rfl, rfl⟩
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      exact ⟨Step.lDivertAbort (s := s') n f' ι₀ κ v hreach' hf' hl' ht', rfl, rfl⟩
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, c) := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      exact ⟨Step.lDivertLand (s := s') n f' ι₀ κ v δ hinv c hreach' hf' hl' ht' hstep', rfl, rfl⟩
  | lLeave n f κ v hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .active κ v := by
        have hlc : Lifecycle.Equiv (.active κ v) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.active_of_active hlc
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      exact ⟨Step.lLeave (s := s') n f' κ v hf' hl' ht', rfl, rfl⟩
  | lUnload n f κ v o hf hl hg =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .unloading κ v o := by
        have hlc : Lifecycle.Equiv (.unloading κ v o) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.unloading_of_unloading hlc
      have hg' : ¬ Full.relied s'.reg n := by
        intro hbad
        exact hg ((h.relied n).2 hbad)
      exact ⟨Step.lUnload (s := s') n f' κ v o hf' hl' hg', rfl, rfl⟩

/-! ## Lemma 55, next-state half -/

/-- **Lemma 55, conclusion half.**  Under the usual well-formedness and
table-provision invariants, the state reached by a step and the state
reached by its transported counterpart are again observationally
equivalent. -/
theorem step_equiv {s s' : State N K E V} (h : State.Equiv s s')
    (hwf : WellFormed s.reg) (hwf' : WellFormed s'.reg)
    (htp : TableProv s.reg) (htp' : TableProv s'.reg)
    (htc : Registry.TableConfined s.reg) (htc' : Registry.TableConfined s'.reg)
    (st : Step s) : ∃ st' : Step s', st'.name = st.name ∧ st'.kind = st.kind ∧
      State.Equiv (Step.next st) (Step.next st') := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      have hn' : lookup s'.reg n = none := h.lookup_none hn
      have hp' : ∀ n' ∈ p, ∃ f', lookup s'.reg n' = some f' := by
        intro n' hn'p
        rcases hp n' hn'p with ⟨f, hf⟩
        exact h.lookup_some hf
      have hdisj' : ∀ n' f', lookup s'.reg n' = some f' →
          (∀ k ∈ c.prov, ∀ k' ∈ f'.comp.prov, k ≠ k') := by
        intro n' f' hf'
        rcases h.lookup_some_symm hf' with ⟨f, hf⟩
        have hff := h.fields n' f f' hf hf'
        have hd := hdisj n' f hf
        rw [hff.comp] at hd
        exact hd
      let fresh : Fiber N K V E := ⟨c, p, fun _ => none, false, .inactive none⟩
      have hgg : Fiber.Equiv fresh fresh := by
        simp [Fiber.Equiv, Lifecycle.Equiv, fresh]
      have hno : ∀ k, (match fresh.lc with | .active _ _ => fresh.table k | _ => none) = none := by
        intro k; simp [fresh]
      have hnoP : ∀ k, (match fresh.lc with | .active _ _ => (fresh.table k).isSome | _ => False) = False := by
        intro k; simp [fresh]
      exact ⟨Step.oInsert (s := s') n c p hn' hp' hdisj', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hn, hn', fresh] using
          (State.Equiv.fresh_set h hn hn' hgg hno hno hnoP hnoP)⟩
  | oRetire n f hf =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      let g : Fiber N K V E := { f with retired := true }
      let g' : Fiber N K V E := { f' with retired := true }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, by simp [g, g'], hff.table, hff.lc⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g']
      exact ⟨Step.oRetire (s := s') n f' hf', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | oRemove n f o hf hl hchild =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .inactive o := by
        have hlc : Lifecycle.Equiv (.inactive o) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.inactive_of_inactive hlc
      have hchild' : ∀ n' f', lookup s'.reg n' = some f' → f'.parent ≠ some n := by
        intro n' f' hf'
        rcases h.lookup_some_symm hf' with ⟨f₀, hf₀⟩
        have hff' := h.fields n' f₀ f' hf₀ hf'
        rw [← hff'.parent]
        exact hchild n' f₀ hf₀
      have hin_r := all_inactive_of_lookup_inactive h.nodup hf hl
      have hin_r' := all_inactive_of_lookup_inactive h.nodup' hf' hl'
      have hdel_sig_r : Full.sigmaOf (Cordix.Full.del s.reg n) = Full.sigmaOf s.reg :=
        sigmaOf_del_eq_of_all_inactive s.reg n hin_r
      have hdel_sig_r' : Full.sigmaOf (Cordix.Full.del s'.reg n) = Full.sigmaOf s'.reg :=
        sigmaOf_del_eq_of_all_inactive s'.reg n hin_r'
      have hdel_prov_r : Full.providerOf (Cordix.Full.del s.reg n) = Full.providerOf s.reg :=
        providerOf_del_eq_of_all_inactive s.reg n hin_r
      have hdel_prov_r' : Full.providerOf (Cordix.Full.del s'.reg n) = Full.providerOf s'.reg :=
        providerOf_del_eq_of_all_inactive s'.reg n hin_r'
      have hnext : State.Equiv (State.del s n) (State.del s' n) := by
        apply State.Equiv.of_registry
        · exact nodupKeys_del s.reg n h.nodup
        · exact nodupKeys_del s'.reg n h.nodup'
        · exact h.ambient
        · calc
            Full.sigmaOf (Cordix.Full.del s.reg n) = Full.sigmaOf s.reg := hdel_sig_r
            _ = Full.sigmaOf s'.reg := h.sigmaOf
            _ = Full.sigmaOf (Cordix.Full.del s'.reg n) := hdel_sig_r'.symm
        · calc
            Full.providerOf (Cordix.Full.del s.reg n) = Full.providerOf s.reg := hdel_prov_r
            _ = Full.providerOf s'.reg := h.providerOf
            _ = Full.providerOf (Cordix.Full.del s'.reg n) := hdel_prov_r'.symm
        · exact domain_del h.domain
        · exact fields_del h.fields
      exact ⟨Step.oRemove (s := s') n f' o hf' hl' hchild', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, State.del] using hnext⟩
  | lBegin n f v hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .inactive none := by
        have hlc : Lifecycle.Equiv (.inactive none) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.inactive_of_inactive hlc
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      let g : Fiber N K V E := { f with lc := .loading f.comp.iter id v }
      let g' : Fiber N K V E := { f' with lc := .loading f'.comp.iter id v }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, hff.table, by
          simp [g, g', Lifecycle.Equiv, hff.comp]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      exact ⟨Step.lBegin (s := s') n f' v hf' hl' ht', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, some ι') := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      let g : Fiber N K V E := { f with table := δ, lc := .loading ι' (κ ∘ hinv) v }
      let g' : Fiber N K V E := { f' with table := δ, lc := .loading ι' (κ ∘ hinv) v }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, by simp [g, g'], by
          simp [g, g', Lifecycle.Equiv]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      exact ⟨Step.lIter (s := s') n f' ι₀ κ v ι' δ hinv hreach' hf' hl' ht' hstep', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', set_set_eq, g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Full.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, none) := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      let g : Fiber N K V E := { f with table := δ, lc := .active (κ ∘ hinv) v }
      let g' : Fiber N K V E := { f' with table := δ, lc := .active (κ ∘ hinv) v }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, by simp [g, g'], by
          simp [g, g', Lifecycle.Equiv]⟩
      have hnext_reg_r : (Step.next (Step.lFinish (s := s) n f ι κ v δ hinv hreach hf hl ht hstep)).reg =
          Cordix.Full.set s.reg n g := by
        simp [Step.next, Step.edit, Step.psi, hf, set_set_eq, g]
      have hnext_reg_r' : (Step.next (Step.lFinish (s := s') n f' ι₀ κ v δ hinv hreach' hf' hl' ht' hstep')).reg =
          Cordix.Full.set s'.reg n g' := by
        simp [Step.next, Step.edit, Step.psi, hf', set_set_eq, g']
      have hsig : Full.sigmaOf (Cordix.Full.set s.reg n g) = Full.sigmaOf (Cordix.Full.set s'.reg n g') := by
        funext k
        by_cases hk : (δ k).isSome
        · have hs1 := sigmaOf_set_active_eq_of_delta_some h.nodup hwf htp (htc n f hf) hf hl hreach hstep hk
          have hs2 := sigmaOf_set_active_eq_of_delta_some h.nodup' hwf' htp' (htc' n f' hf') hf' hl' hreach' hstep' hk
          exact hs1.trans hs2.symm
        · have hk_none : δ k = none := Option.not_isSome_iff_eq_none.mp hk
          have hs1 := sigmaOf_set_active_eq_sigmaOf_of_delta_none (hinv := hinv) h.nodup hf hl hk_none
          have hs2 := sigmaOf_set_active_eq_sigmaOf_of_delta_none (hinv := hinv) h.nodup' hf' hl' hk_none
          calc
            Full.sigmaOf (Cordix.Full.set s.reg n g) k = Full.sigmaOf s.reg k := hs1
            _ = Full.sigmaOf s'.reg k := by exact congrFun h.sigmaOf k
            _ = Full.sigmaOf (Cordix.Full.set s'.reg n g') k := hs2.symm
      have hprov : Full.providerOf (Cordix.Full.set s.reg n g) = Full.providerOf (Cordix.Full.set s'.reg n g') := by
        funext k
        by_cases hk : (δ k).isSome
        · have hp1 := providerOf_set_active_eq_of_delta_some h.nodup hwf htp (htc n f hf) hf hl hreach hstep hk
          have hp2 := providerOf_set_active_eq_of_delta_some h.nodup' hwf' htp' (htc' n f' hf') hf' hl' hreach' hstep' hk
          exact hp1.trans hp2.symm
        · have hk_none : δ k = none := Option.not_isSome_iff_eq_none.mp hk
          have hp1 := providerOf_set_active_eq_sigmaOf_of_delta_none (hinv := hinv) h.nodup hf hl hk_none
          have hp2 := providerOf_set_active_eq_sigmaOf_of_delta_none (hinv := hinv) h.nodup' hf' hl' hk_none
          calc
            Full.providerOf (Cordix.Full.set s.reg n g) k = Full.providerOf s.reg k := hp1
            _ = Full.providerOf s'.reg k := by exact congrFun h.providerOf k
            _ = Full.providerOf (Cordix.Full.set s'.reg n g') k := hp2.symm
      have hnext : State.Equiv ⟨Cordix.Full.set s.reg n g, s.ambient⟩
          ⟨Cordix.Full.set s'.reg n g', s'.ambient⟩ := by
        apply State.Equiv.of_registry
        · exact nodupKeys_set s.reg n g h.nodup
        · exact nodupKeys_set s'.reg n g' h.nodup'
        · exact h.ambient
        · exact hsig
        · exact hprov
        · exact domain_set h.domain
        · exact fields_set h.fields hgg
      exact ⟨Step.lFinish (s := s') n f' ι₀ κ v δ hinv hreach' hf' hl' ht' hstep', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', set_set_eq, g, g'] using hnext⟩
  | lRaise n f ι κ v e hreach hf hl hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) = .error e := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      let g : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      let g' : Fiber N K V E := { f' with lc := .unloading κ v (some e) }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, hff.table, by
          simp [g, g', Lifecycle.Equiv]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      exact ⟨Step.lRaise (s := s') n f' ι₀ κ v e hreach' hf' hl' hstep', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      let g : Fiber N K V E := { f with lc := .unloading κ v none }
      let g' : Fiber N K V E := { f' with lc := .unloading κ v none }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, hff.table, by
          simp [g, g', Lifecycle.Equiv]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      exact ⟨Step.lDivertAbort (s := s') n f' ι₀ κ v hreach' hf' hl' ht', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      have hstep' : Cordix.Iterator.step ι₀ (Full.sigmaOf s'.reg) =
          .ok (δ, hinv, c) := by
        rw [← hι]
        simpa [h.sigmaOf] using hstep
      let g : Fiber N K V E := { f with table := δ, lc := .unloading (κ ∘ hinv) v none }
      let g' : Fiber N K V E := { f' with table := δ, lc := .unloading (κ ∘ hinv) v none }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, by simp [g, g'], by
          simp [g, g', Lifecycle.Equiv]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      exact ⟨Step.lDivertLand (s := s') n f' ι₀ κ v δ hinv c hreach' hf' hl' ht' hstep', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', set_set_eq, g, g'] using
          (State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov')⟩
  | lLeave n f κ v hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .active κ v := by
        have hlc : Lifecycle.Equiv (.active κ v) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.active_of_active hlc
      have ht' : Full.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Full.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      let g : Fiber N K V E := { f with lc := .unloading κ v none }
      let g' : Fiber N K V E := { f' with lc := .unloading κ v none }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, hff.table, by
          simp [g, g', Lifecycle.Equiv]⟩
      have hsig : Full.sigmaOf (Cordix.Full.set s.reg n g) = Full.sigmaOf (Cordix.Full.set s'.reg n g') := by
        funext k
        by_cases hk : (f.table k).isSome
        · have hs1 := sigmaOf_set_unloading_eq_none h.nodup hwf htp hf hl hk
          have hs2 := sigmaOf_set_unloading_eq_none h.nodup' hwf' htp' hf' hl'
              (by simpa [hff.table] using hk)
          exact hs1.trans hs2.symm
        · have hk_none : f.table k = none := Option.not_isSome_iff_eq_none.mp hk
          have hk_none' : f'.table k = none := by rw [← hff.table]; exact hk_none
          have hs1 := sigmaOf_set_eq_of_sigmaContrib_eq_k h.nodup hf
            (by
              change Fiber.sigmaContrib g k = Fiber.sigmaContrib f k
              simp [Fiber.sigmaContrib, g, hl, hk_none])
          have hs2 := sigmaOf_set_eq_of_sigmaContrib_eq_k h.nodup' hf'
            (by
              change Fiber.sigmaContrib g' k = Fiber.sigmaContrib f' k
              simp [Fiber.sigmaContrib, g', hl', hk_none'])
          calc
            Full.sigmaOf (Cordix.Full.set s.reg n g) k = Full.sigmaOf s.reg k := hs1
            _ = Full.sigmaOf s'.reg k := by exact congrFun h.sigmaOf k
            _ = Full.sigmaOf (Cordix.Full.set s'.reg n g') k := hs2.symm
      have hprov : Full.providerOf (Cordix.Full.set s.reg n g) = Full.providerOf (Cordix.Full.set s'.reg n g') := by
        funext k
        by_cases hk : (f.table k).isSome
        · have hp1 := providerOf_set_unloading_eq_none h.nodup hwf htp hf hl hk
          have hp2 := providerOf_set_unloading_eq_none h.nodup' hwf' htp' hf' hl'
              (by simpa [hff.table] using hk)
          exact hp1.trans hp2.symm
        · have hk_none : f.table k = none := Option.not_isSome_iff_eq_none.mp hk
          have hk_none' : f'.table k = none := by rw [← hff.table]; exact hk_none
          have hp1 := providerOf_set_eq_of_provContrib_eq_k h.nodup hf
            (by
              change Fiber.provContrib g k = Fiber.provContrib f k
              simp [Fiber.provContrib, g, hl, hk_none])
          have hp2 := providerOf_set_eq_of_provContrib_eq_k h.nodup' hf'
            (by
              change Fiber.provContrib g' k = Fiber.provContrib f' k
              simp [Fiber.provContrib, g', hl', hk_none'])
          calc
            Full.providerOf (Cordix.Full.set s.reg n g) k = Full.providerOf s.reg k := hp1
            _ = Full.providerOf s'.reg k := by exact congrFun h.providerOf k
            _ = Full.providerOf (Cordix.Full.set s'.reg n g') k := hp2.symm
      have hnext : State.Equiv ⟨Cordix.Full.set s.reg n g, s.ambient⟩
          ⟨Cordix.Full.set s'.reg n g', s'.ambient⟩ := by
        apply State.Equiv.of_registry
        · exact nodupKeys_set s.reg n g h.nodup
        · exact nodupKeys_set s'.reg n g' h.nodup'
        · exact h.ambient
        · exact hsig
        · exact hprov
        · exact domain_set h.domain
        · exact fields_set h.fields hgg
      exact ⟨Step.lLeave (s := s') n f' κ v hf' hl' ht', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using hnext⟩
  | lUnload n f κ v o hf hl hg =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .unloading κ v o := by
        have hlc : Lifecycle.Equiv (.unloading κ v o) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.unloading_of_unloading hlc
      have hg' : ¬ Full.relied s'.reg n := by
        intro hbad
        exact hg ((h.relied n).2 hbad)
      let g : Fiber N K V E := { f with lc := .inactive o }
      let g' : Fiber N K V E := { f' with lc := .inactive o }
      have hgg : Fiber.Equiv g g' := by
        exact ⟨hff.comp, hff.parent, hff.retired, hff.table, by
          simp [g, g', Lifecycle.Equiv]⟩
      have hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                    (match f.lc with | .active _ _ => f.table k | _ => none) := by
        intro k; simp [g, hl]
      have hcg' : ∀ k, (match g'.lc with | .active _ _ => g'.table k | _ => none) =
                     (match f'.lc with | .active _ _ => f'.table k | _ => none) := by
        intro k; simp [g', hl']
      have hprov : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
                      (match f.lc with | .active _ _ => (f.table k).isSome | _ => False) := by
        intro k; simp [g, hl]
      have hprov' : ∀ k, (match g'.lc with | .active _ _ => (g'.table k).isSome | _ => False) ↔
                       (match f'.lc with | .active _ _ => (f'.table k).isSome | _ => False) := by
        intro k; simp [g', hl']
      have hreg : State.Equiv ⟨Cordix.Full.set s.reg n g, s.ambient⟩
          ⟨Cordix.Full.set s'.reg n g', s'.ambient⟩ :=
        State.Equiv.set h hf hf' hgg hcg hcg' hprov hprov'
      have hnext : State.Equiv ⟨Cordix.Full.set s.reg n g, κ s.ambient⟩
          ⟨Cordix.Full.set s'.reg n g', κ s'.ambient⟩ := by
        apply State.Equiv.of_registry
        · exact hreg.nodup
        · exact hreg.nodup'
        · exact by rw [h.ambient]
        · exact hreg.sigmaOf
        · exact hreg.providerOf
        · exact hreg.domain
        · exact hreg.fields
      exact ⟨Step.lUnload (s := s') n f' κ v o hf' hl' hg', rfl, rfl, by
        simpa [Step.next, Step.edit, Step.psi, hf, hf', g, g'] using hnext⟩

end Full

end Cordix
