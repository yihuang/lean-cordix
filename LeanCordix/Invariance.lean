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

end Full

end Cordix
