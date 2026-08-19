import LeanCordix.Basic
import LeanCordix.Step
import LeanCordix.TableConfined
import LeanCordix.Vestigial
import LeanCordix.WellFormed

/-!
# LeanCordix.Invariance — Lemma 55: observational state equivalence and step transport

This file ports the deleted legacy `Invariance.lean` metatheory onto the
current faithful full-context model.

The current faithful `Step` records run their iterators on
`State.fullCtx` (ambient paired with the raw sigma), so the observational
equivalence used here includes equality of the full context as well as the
classical active-sigma observations (`sigmaOf`, `providerOf`, `targetOf`,
`relied`) and the rule-visible fiber fields.

The main result is `step_transport`: if two states are observationally
equivalent then every step applicable at one state is applicable at the
other with the same acting name and rule kind.

We also provide a derived `step_equiv` form: the next-state half of Lemma 55
is stated relative to a caller-supplied preservation obligation, because in
the faithful model the effect-producing rules additionally require
confinement/table side conditions that are not part of `State.Equiv` itself.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- Two iterators with the same full-context step function are equal. -/
theorem Iterator.eq_of_step_eq {ι ι' : Iterator (Ctx K V) E}
    (h : ∀ γ, Iterator.step ι γ = Iterator.step ι' γ) : ι = ι' := by
  cases ι with
  | mk run =>
  cases ι' with
  | mk run' =>
    congr
    funext γ
    exact h γ

/-- Observational equivalence of lifecycle states.  Iterators are compared
by their full step functions; accumulators and committed views must agree. -/
def Lifecycle.Equiv : Lifecycle N K V E → Lifecycle N K V E → Prop
  | .inactive o, .inactive o' => o = o'
  | .loading ι κ v, .loading ι' κ' v' =>
      (∀ γ : Ctx K V, Iterator.step ι γ = Iterator.step ι' γ) ∧ κ = κ' ∧ v = v'
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
  cases lc with
  | inactive o =>
      cases lc' with
      | inactive o' => simp [Lifecycle.Equiv] at h ⊢; exact h.symm
      | loading ι κ v => simp [Lifecycle.Equiv] at h
      | active κ v => simp [Lifecycle.Equiv] at h
      | unloading κ v o' => simp [Lifecycle.Equiv] at h
  | loading ι κ v =>
      cases lc' with
      | inactive o => simp [Lifecycle.Equiv] at h
      | loading ι' κ' v' =>
          change (∀ γ : Ctx K V, Iterator.step ι γ = Iterator.step ι' γ) ∧ κ = κ' ∧ v = v' at h
          rcases h with ⟨hstep, hκ, hv⟩
          exact ⟨fun γ => (hstep γ).symm, hκ.symm, hv.symm⟩
      | active κ' v' => simp [Lifecycle.Equiv] at h
      | unloading κ' v' o' => simp [Lifecycle.Equiv] at h
  | active κ v =>
      cases lc' with
      | inactive o => simp [Lifecycle.Equiv] at h
      | loading ι κ' v' => simp [Lifecycle.Equiv] at h
      | active κ' v' =>
          change κ = κ' ∧ v = v' at h
          rcases h with ⟨hκ, hv⟩; exact ⟨hκ.symm, hv.symm⟩
      | unloading κ' v' o' => simp [Lifecycle.Equiv] at h
  | unloading κ v o =>
      cases lc' with
      | inactive o' => simp [Lifecycle.Equiv] at h
      | loading ι κ' v' => simp [Lifecycle.Equiv] at h
      | active κ' v' => simp [Lifecycle.Equiv] at h
      | unloading κ' v' o' =>
          change κ = κ' ∧ v = v' ∧ o = o' at h
          rcases h with ⟨hκ, hv, ho⟩; exact ⟨hκ.symm, hv.symm, ho.symm⟩

theorem inactive_of_inactive {o : Option E} {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.inactive o) lc') : lc' = .inactive o := by
  cases lc' with
  | inactive o' => simp [Lifecycle.Equiv] at h; rw [← h]
  | loading ι κ v => simp [Lifecycle.Equiv] at h
  | active κ v => simp [Lifecycle.Equiv] at h
  | unloading κ v o' => simp [Lifecycle.Equiv] at h

theorem loading_of_loading {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {lc' : Lifecycle N K V E}
    (h : Lifecycle.Equiv (.loading ι κ v) lc') :
    ∃ ι', lc' = .loading ι' κ v ∧ ι = ι' := by
  cases lc' with
  | inactive o => simp [Lifecycle.Equiv] at h
  | loading ι' κ' v' =>
      change (∀ γ : Ctx K V, Iterator.step ι γ = Iterator.step ι' γ) ∧ κ = κ' ∧ v = v' at h
      rcases h with ⟨hstep, hκ, hv⟩
      subst κ'
      subst v'
      exact ⟨ι', rfl, Iterator.eq_of_step_eq hstep⟩
  | active κ' v' => simp [Lifecycle.Equiv] at h
  | unloading κ' v' o' => simp [Lifecycle.Equiv] at h

theorem active_of_active {κ : Ctx K V → Ctx K V} {v : K → Option N}
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

theorem unloading_of_unloading {κ : Ctx K V → Ctx K V} {v : K → Option N}
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

/-- Observational equivalence of faithful states.

This is the current-model analogue of the old `Full.State.Equiv`.  In
addition to the active observations, it records equality of the full context
(`ambient`, `rawSigma`), which is what the faithful iterator rules read. -/
structure State.Equiv (s s' : State N K E V) : Prop where
  nodup : NodupKeys s.reg
  nodup' : NodupKeys s'.reg
  fullCtx : State.fullCtx s = State.fullCtx s'
  sigmaOf : Cordix.sigmaOf s.reg = Cordix.sigmaOf s'.reg
  providerOf : Cordix.providerOf s.reg = Cordix.providerOf s'.reg
  targetOf : ∀ n, Cordix.targetOf s.reg n = Cordix.targetOf s'.reg n
  relied : ∀ n, Cordix.relied s.reg n ↔ Cordix.relied s'.reg n
  domain : ∀ n, (lookup s.reg n).isSome ↔ (lookup s'.reg n).isSome
  fields : ∀ n f f', lookup s.reg n = some f → lookup s'.reg n = some f' →
    Fiber.Equiv f f'

namespace State.Equiv

theorem ambient {s s' : State N K E V} (h : State.Equiv s s') :
    s.ambient = s'.ambient := by
  have hf := congrArg Prod.fst h.fullCtx
  simpa [State.fullCtx] using hf

theorem rawSigma {s s' : State N K E V} (h : State.Equiv s s') :
    rawSigma s.reg = rawSigma s'.reg := by
  have hf := congrArg Prod.snd h.fullCtx
  simpa [State.fullCtx] using hf

theorem symm {s s' : State N K E V} (h : State.Equiv s s') : State.Equiv s' s where
  nodup := h.nodup'
  nodup' := h.nodup
  fullCtx := h.fullCtx.symm
  sigmaOf := h.sigmaOf.symm
  providerOf := h.providerOf.symm
  targetOf := fun n => (h.targetOf n).symm
  relied := fun n => (h.relied n).symm
  domain := fun n => (h.domain n).symm
  fields := fun n f' f hf' hf => Fiber.Equiv.symm (h.fields n f f' hf hf')

theorem lookup_some {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    {f : Fiber N K V E} (hf : lookup s.reg n = some f) :
    ∃ f', lookup s'.reg n = some f' := by
  have hn : (lookup s'.reg n).isSome := (h.domain n).mp (by rw [hf]; simp)
  exact Option.isSome_iff_exists.mp hn

theorem lookup_some_symm {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    {f' : Fiber N K V E} (hf' : lookup s'.reg n = some f') :
    ∃ f, lookup s.reg n = some f :=
  h.symm.lookup_some hf'

theorem lookup_none {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    (hn : lookup s.reg n = none) : lookup s'.reg n = none := by
  by_cases h' : (lookup s'.reg n).isSome
  · rcases Option.isSome_iff_exists.mp h' with ⟨f', hf'⟩
    rcases h.lookup_some_symm hf' with ⟨f, hf⟩
    rw [hn] at hf
    simp at hf
  · exact Option.not_isSome_iff_eq_none.mp h'

theorem lookup_none_symm {s s' : State N K E V} (h : State.Equiv s s') {n : N}
    (hn : lookup s'.reg n = none) : lookup s.reg n = none :=
  h.symm.lookup_none hn

end State.Equiv

/-! ## Congruence helpers for `targetOf` and `relied` -/

theorem targetOf_congr {r r' : Registry N K V E}
    (hsig : Cordix.sigmaOf r = Cordix.sigmaOf r')
    (hprov : Cordix.providerOf r = Cordix.providerOf r')
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    (hfields : ∀ n f f', lookup r n = some f → lookup r' n = some f' →
      Fiber.Equiv f f') :
    ∀ n, Cordix.targetOf r n = Cordix.targetOf r' n := by
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
      simp [Cordix.targetOf, hlook, hlook']
  | some f =>
      rcases Option.isSome_iff_exists.mp ((hdom n).mp (by simp [hlook])) with ⟨f', hf'⟩
      have hff := hfields n f f' hlook hf'
      simp [Cordix.targetOf, hlook, hf', hff.comp, hff.retired, hsig, hprov]

theorem relied_congr {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    (hfields : ∀ n f f', lookup r n = some f → lookup r' n = some f' →
      Fiber.Equiv f f') :
    ∀ n, Cordix.relied r n ↔ Cordix.relied r' n := by
  intro n
  unfold Cordix.relied
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

theorem domain_set {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome)
    {n : N} {g g' : Fiber N K V E} :
    ∀ m, (lookup (set r n g) m).isSome ↔ (lookup (set r' n g') m).isSome := by
  intro m
  by_cases hmn : m = n
  · subst m
    simp [lookup_set_eq]
  · simp [lookup_set_ne r n m g hmn, lookup_set_ne r' n m g' hmn, hdom m]

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

theorem domain_del {r r' : Registry N K V E}
    (hdom : ∀ n, (lookup r n).isSome ↔ (lookup r' n).isSome) {n : N} :
    ∀ m, (lookup (del r n) m).isSome ↔ (lookup (del r' n) m).isSome := by
  intro m
  by_cases hmn : m = n
  · subst m
    simp [lookup_del_self]
  · simp [lookup_del_ne (r := r) (n := n) (m := m) hmn, lookup_del_ne (r := r') (n := n) (m := m) hmn, hdom m]

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

/-- Assemble `State.Equiv` from equality of the ambient context, the raw
sigma, and the registry-level observations. -/
theorem State.Equiv.of_registry {s s' : State N K E V}
    (hn : NodupKeys s.reg) (hn' : NodupKeys s'.reg)
    (hamb : s.ambient = s'.ambient)
    (hraw : Cordix.rawSigma s.reg = Cordix.rawSigma s'.reg)
    (hsig : Cordix.sigmaOf s.reg = Cordix.sigmaOf s'.reg)
    (hprov : Cordix.providerOf s.reg = Cordix.providerOf s'.reg)
    (hdom : ∀ n, (lookup s.reg n).isSome ↔ (lookup s'.reg n).isSome)
    (hfields : ∀ n f f', lookup s.reg n = some f → lookup s'.reg n = some f' →
      Fiber.Equiv f f') :
    State.Equiv s s' where
  nodup := hn
  nodup' := hn'
  fullCtx := by
    simp [State.fullCtx, hamb, hraw]
  sigmaOf := hsig
  providerOf := hprov
  targetOf := targetOf_congr hsig hprov hdom hfields
  relied := relied_congr hdom hfields
  domain := hdom
  fields := hfields

theorem sigmaOf_set_eq_sigmaOf_of_contrib_eq {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E}
    (hf : lookup r n = some f)
    (hcg : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) =
                (match f.lc with | .active _ _ => f.table k | _ => none)) :
    Cordix.sigmaOf (set r n g) = Cordix.sigmaOf r := by
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
        rw [show Cordix.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.set, hpn]]
        have hcons : Cordix.sigmaOf ((n, g) :: rest) k = Cordix.sigmaOf ((n, p.2) :: rest) k := by
          cases hg : g.lc <;> cases hp : p.2.lc <;>
            simp [Cordix.sigmaOf, List.foldr, hg, hp] at hcg' ⊢
          case inactive.active => rw [← hcg']; rfl
          case loading.active => rw [← hcg']; rfl
          case unloading.active => rw [← hcg']; rfl
          case active.inactive => rw [hcg']; rfl
          case active.loading => rw [hcg']; rfl
          case active.unloading => rw [hcg']; rfl
          case active.active => rw [hcg']
        change Cordix.sigmaOf ((n, g) :: rest) k = Cordix.sigmaOf ((p.1, p.2) :: rest) k
        rw [hpn]
        exact hcons
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
          simp [Cordix.set, hpn]]
        exact sigmaOf_cons_congr_k p k (ih hn_rest hf_rest)

/-- Helper for `providerOf_set_eq_providerOf_of_contrib_eq`: equal provider
contributions at the head give equal `providerOf` folds. -/
theorem providerOf_cons_eq_of_contrib_eq {n : N} {g : Fiber N K V E}
    {p : N × Fiber N K V E} (rest : Registry N K V E) {k : K}
    (hcg : (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) ↔
           (match p.2.lc with | .active _ _ => (p.2.table k).isSome | _ => False)) :
    Cordix.providerOf ((n, g) :: rest) k = Cordix.providerOf ((n, p.2) :: rest) k := by
  cases hg : g.lc <;> cases hp : p.2.lc <;>
    simp [Cordix.providerOf, List.foldr, hg, hp] at hcg ⊢
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
    Cordix.providerOf (set r n g) = Cordix.providerOf r := by
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
        rw [show Cordix.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.set, hpn]]
        change Cordix.providerOf ((n, g) :: rest) k = Cordix.providerOf ((p.1, p.2) :: rest) k
        rw [hpn]
        exact providerOf_cons_eq_of_contrib_eq rest hcg'
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
          simp [Cordix.set, hpn]]
        exact providerOf_cons_congr_k p k (ih hn_rest hf_rest)

/-- Inserting a fresh inactive fiber does not change `sigmaOf`. -/
theorem sigmaOf_set_fresh_eq {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    (hn : lookup r n = none)
    (hno : ∀ k, (match g.lc with | .active _ _ => g.table k | _ => none) = none) :
    Cordix.sigmaOf (set r n g) = Cordix.sigmaOf r := by
  funext k
  induction r with
  | nil =>
      cases hg : g.lc <;> simp [Cordix.set, Cordix.sigmaOf, List.foldr, hg]
      case active => simpa [hg] using hno k
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        have : lookup (p :: rest) n = some p.2 := by simp [lookup, hEq]
        rw [hn] at this
        simp at this
      have hn_rest : lookup rest n = none := by
        simpa [lookup, hpn] using hn
      rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
        simp [Cordix.set, hpn]]
      exact sigmaOf_cons_congr_k p k (ih hn_rest)

/-- Inserting a fresh inactive fiber does not change `providerOf`. -/
theorem providerOf_set_fresh_eq {r : Registry N K V E} {n : N} {g : Fiber N K V E}
    (hn : lookup r n = none)
    (hno : ∀ k, (match g.lc with | .active _ _ => (g.table k).isSome | _ => False) = False) :
    Cordix.providerOf (set r n g) = Cordix.providerOf r := by
  funext k
  induction r with
  | nil =>
      cases hg : g.lc <;> simp [Cordix.set, Cordix.providerOf, List.foldr, hg]
      case active => simpa [hg] using hno k
  | cons p rest ih =>
      have hpn : p.1 ≠ n := by
        intro hEq
        have : lookup (p :: rest) n = some p.2 := by simp [lookup, hEq]
        rw [hn] at this
        simp at this
      have hn_rest : lookup rest n = none := by
        simpa [lookup, hpn] using hn
      rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
        simp [Cordix.set, hpn]]
      exact providerOf_cons_congr_k p k (ih hn_rest)

/-- A pointwise update that preserves the sigma/provider contribution of
the acting fiber preserves `State.Equiv`. -/

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

theorem sigmaOf_eq_none_of_no_sigma {r : Registry N K V E} {k : K}
    (h : ∀ p ∈ r, Fiber.sigmaContrib p.2 k = none) :
    Cordix.sigmaOf r k = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      have hp := h p (by simp)
      have hrest : ∀ q ∈ rest, Fiber.sigmaContrib q.2 k = none := by
        intro q hq; exact h q (by simp [hq])
      cases hlc : p.2.lc with
      | inactive o => simpa [Cordix.sigmaOf, List.foldr, hlc] using ih hrest
      | loading ι κ v => simpa [Cordix.sigmaOf, List.foldr, hlc] using ih hrest
      | active κ v =>
          have hp' : p.2.table k = none := by
            simpa [Fiber.sigmaContrib, hlc] using hp
          simpa [Cordix.sigmaOf, List.foldr, hlc, hp'] using ih hrest
      | unloading κ v o => simpa [Cordix.sigmaOf, List.foldr, hlc] using ih hrest

/-- If no fiber contributes to `providerOf` at `k`, then `providerOf r k`
is `none`. -/
theorem providerOf_eq_none_of_no_prov {r : Registry N K V E} {k : K}
    (h : ∀ p ∈ r, Fiber.provContrib p.2 k = false) :
    Cordix.providerOf r k = none := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      have hp := h p (by simp)
      have hrest : ∀ q ∈ rest, Fiber.provContrib q.2 k = false := by
        intro q hq; exact h q (by simp [hq])
      cases hlc : p.2.lc with
      | inactive o => simpa [Cordix.providerOf, List.foldr, hlc] using ih hrest
      | loading ι κ v => simpa [Cordix.providerOf, List.foldr, hlc] using ih hrest
      | active κ v =>
          have hp' : (p.2.table k).isSome = false := by
            simpa [Fiber.provContrib, hlc] using hp
          simpa [Cordix.providerOf, List.foldr, hlc, hp'] using ih hrest
      | unloading κ v o => simpa [Cordix.providerOf, List.foldr, hlc] using ih hrest

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
    {q : N × Fiber N K V E} (hq : q ∈ Cordix.set r n g) (hqn : q.1 ≠ n) :
    q ∈ r := by
  induction r with
  | nil =>
      simp [Cordix.set] at hq
      have hq1 : q.1 = n := by simpa [hq]
      exact absurd hq1 hqn
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · simp [Cordix.set, hpn] at hq
        rcases hq with hEq | hmem
        · have hq1 : q.1 = n := by simpa [hEq]
          exact absurd hq1 hqn
        · exact List.Mem.tail _ hmem
      · simp [Cordix.set, hpn] at hq
        rcases hq with hEq | hmem
        · rw [hEq]
          exact List.Mem.head _
        · exact List.Mem.tail _ (ih hmem)

/-- If the unique active provider of `k` at `n` is unloaded, then `k` has
no provider left. -/

theorem providerOf_set_unloading_eq_none {r : Registry N K V E} (hn : NodupKeys r)
    (hwf : WellFormed r) (htp : TableProv r) {n : N} {f : Fiber N K V E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup r n = some f) (hl : f.lc = .active κ v) {k : K}
    (ht : (f.table k).isSome) :
    Cordix.providerOf (Cordix.set r n { f with lc := .unloading κ v none }) k = none := by
  apply providerOf_eq_none_of_no_prov
  intro q hq
  by_cases hqn : q.1 = n
  · have hq_lookup : lookup (Cordix.set r n { f with lc := .unloading κ v none }) q.1 = some q.2 :=
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
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup r n = some f) (hl : f.lc = .active κ v) {k : K}
    (ht : (f.table k).isSome) :
    Cordix.sigmaOf (Cordix.set r n { f with lc := .unloading κ v none }) k = none := by
  apply sigmaOf_eq_none_of_no_sigma
  intro q hq
  by_cases hqn : q.1 = n
  · have hq_lookup : lookup (Cordix.set r n { f with lc := .unloading κ v none }) q.1 = some q.2 :=
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
    {ι : Iterator (Ctx K V) E} {δ : Ctx K V}
    {hinv : Ctx K V → Ctx K V}
    {c' : Option (Iterator (Ctx K V) E)} {σ : Ctx K V}
    (hconf : Component.TableConfined c)
    (hreach : Iterator.Reachable c.iter ι)
    (hstep : Iterator.step ι σ = .ok (δ, hinv, c')) {k : K}
    (ht : (δ.2 k).isSome) : k ∈ c.prov := by
  have hstepconf := hconf hreach
  have h2 := hstepconf.2 σ ((fun _ => none), (fun _ => none))
  rw [hstep] at h2
  have hk := h2 k ht
  cases hk with
  | inl hnone => exact absurd hnone (by simp)
  | inr hprov => exact hprov

/-- `sigmaOf` of a cons is the head's sigma contribution or the tail's. -/

theorem sigmaOf_cons_eq_of_sigmaContrib {p : N × Fiber N K V E}
    {rest : Registry N K V E} {k : K} :
    Cordix.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Cordix.sigmaOf rest k) := by
  cases hlc : p.2.lc <;> simp [Cordix.sigmaOf, List.foldr, Fiber.sigmaContrib, hlc]

/-- `providerOf` of a cons is the head's provider contribution, or the
tail's. -/
theorem providerOf_cons_eq_of_provContrib {p : N × Fiber N K V E}
    {rest : Registry N K V E} {k : K} :
    Cordix.providerOf (p :: rest) k =
      if Fiber.provContrib p.2 k = true then some p.1 else Cordix.providerOf rest k := by
  cases hlc : p.2.lc <;> simp [Cordix.providerOf, List.foldr, Fiber.provContrib, hlc]

/-- `set` preserves `sigmaOf` at a single key when the old and new fibers
have the same sigma contribution there. -/
theorem sigmaOf_set_eq_of_sigmaContrib_eq_k {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E} {k : K}
    (hf : lookup r n = some f)
    (hcg : Fiber.sigmaContrib g k = Fiber.sigmaContrib f k) :
    Cordix.sigmaOf (Cordix.set r n g) k = Cordix.sigmaOf r k := by
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : Fiber.sigmaContrib g k = Fiber.sigmaContrib p.2 k := by
          simpa [hf_eq] using hcg
        rw [show Cordix.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.set, hpn]]
        rw [sigmaOf_cons_eq_of_sigmaContrib]
        rw [show Cordix.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Cordix.sigmaOf rest k) by
          rw [sigmaOf_cons_eq_of_sigmaContrib]]
        rw [hcg']
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
          simp [Cordix.set, hpn]]
        rw [sigmaOf_cons_eq_of_sigmaContrib]
        rw [show Cordix.sigmaOf (p :: rest) k = (Fiber.sigmaContrib p.2 k).or (Cordix.sigmaOf rest k) by
          rw [sigmaOf_cons_eq_of_sigmaContrib]]
        rw [ih hn_rest hf_rest]

/-- `set` preserves `providerOf` at a single key when the old and new
fibers have the same provider contribution there. -/
theorem providerOf_set_eq_of_provContrib_eq_k {r : Registry N K V E}
    (hn : NodupKeys r) {n : N} {f g : Fiber N K V E} {k : K}
    (hf : lookup r n = some f)
    (hcg : Fiber.provContrib g k = Fiber.provContrib f k) :
    Cordix.providerOf (Cordix.set r n g) k = Cordix.providerOf r k := by
  induction r with
  | nil => simp [lookup] at hf
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · have hf_p : lookup (p :: rest) p.1 = some p.2 := by simp [lookup]
        have hf' : lookup (p :: rest) p.1 = some f := by simpa [hpn] using hf
        have hf_eq : f = p.2 := Option.some.inj (hf'.symm.trans hf_p)
        have hcg' : Fiber.provContrib g k = Fiber.provContrib p.2 k := by
          simpa [hf_eq] using hcg
        rw [show Cordix.set (p :: rest) n g = (n, g) :: rest by
          simp [Cordix.set, hpn]]
        rw [providerOf_cons_eq_of_provContrib]
        rw [show Cordix.providerOf (p :: rest) k = if Fiber.provContrib p.2 k = true then some p.1
          else Cordix.providerOf rest k by
          rw [providerOf_cons_eq_of_provContrib]]
        rw [hcg']
        simp [hpn]
      · have hf_rest : lookup rest n = some f := by
          simpa [lookup, hpn] using hf
        have hn_rest : NodupKeys rest := by
          change ((p.1 :: rest.map (fun x => x.1)).Nodup) at hn
          rw [List.nodup_cons] at hn
          exact hn.2
        rw [show Cordix.set (p :: rest) n g = p :: Cordix.set rest n g by
          simp [Cordix.set, hpn]]
        rw [providerOf_cons_eq_of_provContrib]
        rw [show Cordix.providerOf (p :: rest) k = if Fiber.provContrib p.2 k = true then some p.1
          else Cordix.providerOf rest k by
          rw [providerOf_cons_eq_of_provContrib]]
        rw [ih hn_rest hf_rest]

/-- If one entry contributes `some x` at `k` and all other entries
contribute nothing, then `sigmaOf` is `some x`. -/

theorem sigmaOf_eq_some_of_single {r : Registry N K V E} {k : K} {n : N}
    {g : Fiber N K V E} {x : V k}
    (hnodup : NodupKeys r)
    (hg : Fiber.sigmaContrib g k = some x)
    (hother : ∀ q ∈ r, q.1 ≠ n → Fiber.sigmaContrib q.2 k = none)
    (hmem : (n, g) ∈ r) : Cordix.sigmaOf r k = some x := by
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
        have hrest : Cordix.sigmaOf rest k = none := sigmaOf_eq_none_of_no_sigma hrest_none
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
    (hmem : (n, g) ∈ r) : Cordix.providerOf r k = some n := by
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
        have hrest : Cordix.providerOf rest k = none := providerOf_eq_none_of_no_prov hrest_none
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

theorem sigmaOf_set_active_eq_of_delta_some {s : State N K E V}
    {n : N} {f : Fiber N K V E}
    (hn : NodupKeys s.reg) (hwf : WellFormed s.reg) (htp : TableProv s.reg)
    (hconf : Component.TableConfined f.comp)
    {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V}
    {hinv : Ctx K V → Ctx K V}
    {c : Option (Iterator (Ctx K V) E)}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, hinv, c)) {k : K}
    (ht : (δ.2 k).isSome) :
    Cordix.sigmaOf (Cordix.set s.reg n ({ f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v })) k = δ.2 k := by
  let new : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v }
  rcases Option.isSome_iff_exists.mp ht with ⟨x, hx⟩
  have hkprov : k ∈ f.comp.prov := hconf.delta_prov hreach hstep ht
  have hnew_sigma : Fiber.sigmaContrib new k = some x := by
    simp [Fiber.sigmaContrib, new, hx, splitTable, hkprov]
  have hmem : (n, new) ∈ Cordix.set s.reg n new := by
    exact lookup_some_mem (lookup_set_eq s.reg n new)
  have hother : ∀ q ∈ Cordix.set s.reg n new, q.1 ≠ n → Fiber.sigmaContrib q.2 k = none := by
    intro q hq hqn
    by_cases hsome : Fiber.sigmaContrib q.2 k = none
    · exact hsome
    · exfalso
      have hq_in_r : q ∈ s.reg := mem_set_of_ne hq hqn
      have hq_lookup : lookup s.reg q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome :=
        Fiber.table_isSome_of_provContrib_eq_true
          (Fiber.provContrib_eq_true_of_sigmaContrib_ne_none hsome)
      have hq_prov : k ∈ q.2.comp.prov := htp q.1 q.2 hq_lookup k hq_table
      exact hwf.provDisj n f q.1 q.2 hf hq_lookup (by intro hEq; exact hqn hEq.symm)
        k hkprov k hq_prov rfl
  have hnodup_set : NodupKeys (Cordix.set s.reg n new) := nodupKeys_set s.reg n new hn
  change Cordix.sigmaOf (Cordix.set s.reg n new) k = δ.2 k
  rw [hx]
  exact sigmaOf_eq_some_of_single hnodup_set hnew_sigma hother hmem

/-- `L-Finish` with a non-empty `δ` makes `n` the provider of `k`. -/
theorem providerOf_set_active_eq_of_delta_some {s : State N K E V}
    {n : N} {f : Fiber N K V E}
    (hn : NodupKeys s.reg) (hwf : WellFormed s.reg) (htp : TableProv s.reg)
    (hconf : Component.TableConfined f.comp)
    {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V}
    {hinv : Ctx K V → Ctx K V}
    {c : Option (Iterator (Ctx K V) E)}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, hinv, c)) {k : K}
    (ht : (δ.2 k).isSome) :
    Cordix.providerOf (Cordix.set s.reg n ({ f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v })) k = some n := by
  let new : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v }
  have hkprov : k ∈ f.comp.prov := hconf.delta_prov hreach hstep ht
  have hnew_prov : Fiber.provContrib new k = true := by
    simp [Fiber.provContrib, new, ht, splitTable, hkprov]
  have hmem : (n, new) ∈ Cordix.set s.reg n new := by
    exact lookup_some_mem (lookup_set_eq s.reg n new)
  have hother : ∀ q ∈ Cordix.set s.reg n new, q.1 ≠ n → Fiber.provContrib q.2 k = false := by
    intro q hq hqn
    by_cases hsome : Fiber.provContrib q.2 k = true
    · exfalso
      have hq_in_r : q ∈ s.reg := mem_set_of_ne hq hqn
      have hq_lookup : lookup s.reg q.1 = some q.2 := lookup_self_of_mem_of_nodup hn hq_in_r
      have hq_table : (q.2.table k).isSome := Fiber.table_isSome_of_provContrib_eq_true hsome
      have hq_prov : k ∈ q.2.comp.prov := htp q.1 q.2 hq_lookup k hq_table
      exact hwf.provDisj n f q.1 q.2 hf hq_lookup (by intro hEq; exact hqn hEq.symm)
        k hkprov k hq_prov rfl
    · cases hb : Fiber.provContrib q.2 k <;> simp [hb] at hsome ⊢
  have hnodup_set : NodupKeys (Cordix.set s.reg n new) := nodupKeys_set s.reg n new hn
  exact providerOf_eq_some_of_single hnodup_set hnew_prov hother hmem

theorem sigmaOf_set_active_eq_sigmaOf_of_delta_none {s : State N K E V}
    (hn : NodupKeys s.reg) {n : N} {f : Fiber N K V E}
    {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V}
    {hinv : Ctx K V → Ctx K V}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v) {k : K}
    (ht : δ.2 k = none) :
    Cordix.sigmaOf (Cordix.set s.reg n ({ f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v })) k =
      Cordix.sigmaOf s.reg k := by
  let new : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v }
  have hcg : Fiber.sigmaContrib new k = Fiber.sigmaContrib f k := by
    simp [Fiber.sigmaContrib, new, hl, ht, splitTable]
  exact sigmaOf_set_eq_of_sigmaContrib_eq_k hn hf hcg

/-- `L-Finish` with an empty `δ k` leaves `providerOf` unchanged at `k`. -/
theorem providerOf_set_active_eq_sigmaOf_of_delta_none {s : State N K E V}
    (hn : NodupKeys s.reg) {n : N} {f : Fiber N K V E}
    {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V}
    {hinv : Ctx K V → Ctx K V}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v) {k : K}
    (ht : δ.2 k = none) :
    Cordix.providerOf (Cordix.set s.reg n ({ f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v })) k =
      Cordix.providerOf s.reg k := by
  let new : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2, lc := .active (κ ∘ hinv) v }
  have hcg : Fiber.provContrib new k = Fiber.provContrib f k := by
    simp [Fiber.provContrib, new, hl, ht, splitTable]
  exact providerOf_set_eq_of_provContrib_eq_k hn hf hcg

/-! ## Lemma 55: step transport along observational equivalence -/

/-- **Lemma 55, applicability half.**  If two states are observationally
equivalent, then every step at one state transports to the other state with
the same acting name and rule kind. -/
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
  | lBegin n f v hf hl ht htable =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .inactive none := by
        have hlc : Lifecycle.Equiv (.inactive none) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.inactive_of_inactive hlc
      have ht' : Cordix.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have htable' : f'.table = fun _ => none := by
        rw [← hff.table]
        exact htable
      exact ⟨Step.lBegin (s := s') n f' v hf' hl' ht' htable', rfl, rfl⟩
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Cordix.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Iterator.step ι₀ (State.fullCtx s') =
          .ok (δ, hinv, some ι') := by
        rw [← hι]
        rw [← h.fullCtx]
        exact hstep
      exact ⟨Step.lIter (s := s') n f' ι₀ κ v ι' δ hinv hreach' hf' hl' ht' hstep', rfl, rfl⟩
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hlc : Lifecycle.Equiv (.loading ι κ v) f'.lc := by
        rw [← hl]
        exact hff.lc
      rcases Lifecycle.Equiv.loading_of_loading hlc with ⟨ι₀, hl', hι⟩
      have ht' : Cordix.targetOf s'.reg n = some v := by
        rw [← h.targetOf n]
        exact ht
      have hreach' : Iterator.Reachable f'.comp.iter ι₀ := by
        rw [← hι, ← hff.comp]
        exact hreach
      have hstep' : Iterator.step ι₀ (State.fullCtx s') =
          .ok (δ, hinv, none) := by
        rw [← hι]
        rw [← h.fullCtx]
        exact hstep
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
      have hstep' : Iterator.step ι₀ (State.fullCtx s') = .error e := by
        rw [← hι]
        rw [← h.fullCtx]
        exact hstep
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
      have ht' : Cordix.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Cordix.targetOf s.reg n = some v := by
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
      have ht' : Cordix.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Cordix.targetOf s.reg n = some v := by
          rw [h.targetOf n]
          exact hbad
        exact ht hbad'
      have hstep' : Iterator.step ι₀ (State.fullCtx s') =
          .ok (δ, hinv, c) := by
        rw [← hι]
        rw [← h.fullCtx]
        exact hstep
      exact ⟨Step.lDivertLand (s := s') n f' ι₀ κ v δ hinv c hreach' hf' hl' ht' hstep', rfl, rfl⟩
  | lLeave n f κ v hf hl ht =>
      rcases h.lookup_some hf with ⟨f', hf'⟩
      have hff := h.fields n f f' hf hf'
      have hl' : f'.lc = .active κ v := by
        have hlc : Lifecycle.Equiv (.active κ v) f'.lc := by
          rw [← hl]
          exact hff.lc
        exact Lifecycle.Equiv.active_of_active hlc
      have ht' : Cordix.targetOf s'.reg n ≠ some v := by
        intro hbad
        have hbad' : Cordix.targetOf s.reg n = some v := by
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
      have hg' : ¬ Cordix.relied s'.reg n := by
        intro hbad
        exact hg ((h.relied n).2 hbad)
      exact ⟨Step.lUnload (s := s') n f' κ v o hf' hl' hg', rfl, rfl⟩

/-- **Lemma 55, derived next-state half.**

The full faithful `step_equiv` statement additionally needs confinement and
table-invariant hypotheses for the effect-producing rules.  This derived
form isolates the step-transport part and lets the caller supply exactly
that next-state preservation obligation. -/
theorem step_equiv {s s' : State N K E V} (h : State.Equiv s s')
    (st : Step s)
    (hpres : ∀ st' : Step s', st'.name = st.name → st'.kind = st.kind →
      State.Equiv (Step.next st) (Step.next st')) :
    ∃ st' : Step s', st'.name = st.name ∧ st'.kind = st.kind ∧
      State.Equiv (Step.next st) (Step.next st') := by
  rcases step_transport h st with ⟨st', hname, hkind⟩
  exact ⟨st', hname, hkind, hpres st' hname hkind⟩

end Cordix
