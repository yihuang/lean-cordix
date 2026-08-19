import LeanCordix.WellFormed
import LeanCordix.Progress
import LeanCordix.Trace

/-!
# LeanCordix.TableConfined — confinement/table-confined machinery

This module ports the missing confinement and table-confinement parts of
deleted `FullCalculus.lean` onto the current faithful full-context model.

In the current model every `Step` is already table-aware (`Step.next` applies
`Step.psi` before `Step.edit`), so `Lstep`/`LstepT` are represented as
state-to-state lifecycle steps using `Step.next`.  The core confinement
package is placed in `TableConfined.ConfinedWellFormed` to avoid clashing
with the progress-only `ConfinedWellFormed` defined in `Progress.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Write confinement -/

/-- Every component of a registry is write-confined. -/
def Registry.Confined (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → Component.Confined f.comp

/-- The unfolding lemma for confined iterators in the full-context model. -/
theorem confinedIterator_step {ι : Iterator (Ctx K V) E} {P : List K}
    (h : ConfinedIterator ι P) {σ δ : Ctx K V} {g : Ctx K V → Ctx K V}
    {c : Option (Iterator (Ctx K V) E)}
    (hstep : Iterator.step ι σ = .ok (δ, g, c)) :
    ∀ k, k ∉ P → σ.2 k = δ.2 k := by
  unfold ConfinedIterator at h
  have := h σ
  rw [hstep] at this
  exact this

/-- A confined component's successful iteration writes only provision
keys. -/
theorem component_confined_step {c : Component K V E}
    (h : Component.Confined c) {σ δ : Ctx K V}
    {g : Ctx K V → Ctx K V}
    {c' : Option (Iterator (Ctx K V) E)}
    (hstep : Iterator.step c.iter σ = .ok (δ, g, c')) :
    ∀ k, k ∉ c.prov → σ.2 k = δ.2 k :=
  confinedIterator_step (h (Iterator.Reachable.self c.iter)) hstep

/-! ## Table confinement for iterators and components -/

/-- One-step table confinement for an iterator: it is confined (writes only
provision keys) and never produces a key that was neither already in the
fiber table nor in the provision.  The statement uses the sigma component
(`.2`) of the full context. -/
def Iterator.TableConfinedStep (ι : Iterator (Ctx K V) E) (P : List K) : Prop :=
  ConfinedIterator ι P ∧
    ∀ σ τ : Ctx K V, match Iterator.step ι σ with
      | .ok (δ, _, _) => ∀ k, (δ.2 k).isSome → (τ.2 k).isSome ∨ k ∈ P
      | .error _ => True

/-- Full table confinement for an iterator: every reachable continuation
is table-confined stepwise. -/
def Iterator.TableConfinedAll (ι : Iterator (Ctx K V) E) (P : List K) : Prop :=
  ∀ {ι'}, Iterator.Reachable ι ι' → Iterator.TableConfinedStep ι' P

/-- Stronger table confinement for a component: every reachable iterator
is table-confined stepwise. -/
def Component.TableConfined (c : Component K V E) : Prop :=
  Iterator.TableConfinedAll c.iter c.prov

/-- Every component of a registry is table-confined. -/
def Registry.TableConfined (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → Component.TableConfined f.comp

/-! ## Target helpers used by the view-invariant preservation lemmas -/

/-- A provider is an active fiber whose table defines the key. -/
theorem providerOf_some_lookup_active_table {r : Registry N K V E} {k : K} {m : N}
    (hn : NodupKeys r) (h : providerOf r k = some m) :
    ∃ g : Fiber N K V E, lookup r m = some g ∧
      ∃ κ v, g.lc = .active κ v ∧ (g.table k).isSome := by
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
          rcases ih hnrest h with ⟨g, hg, κ, v, hlcg, htbl⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          exact ⟨g, by simpa [lookup, hpm] using hg, κ, v, hlcg, htbl⟩
      | loading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, κ, v, hlcg, htbl⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          exact ⟨g, by simpa [lookup, hpm] using hg, κ, v, hlcg, htbl⟩
      | active κ v =>
          simp [providerOf, hlc] at h
          by_cases htbl : (p.2.table k).isSome
          · simp [htbl] at h
            have hpm : p.1 = m := h
            exact ⟨p.2, by simp [lookup, hpm], κ, v, hlc, htbl⟩
          · simp [htbl] at h
            rcases ih hnrest h with ⟨g, hg, κ, v, hlcg, htblg⟩
            have hpm : p.1 ≠ m := by
              intro hEq
              have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
              change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
              rw [List.nodup_cons] at hn
              exact hn.1 (by simpa [hEq] using hm)
            exact ⟨g, by simpa [lookup, hpm] using hg, κ, v, hlcg, htblg⟩
      | unloading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, κ, v, hlcg, htbl⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          exact ⟨g, by simpa [lookup, hpm] using hg, κ, v, hlcg, htbl⟩

/-- The target view of a fiber only names keys in its specification. -/
theorem viewSpec_target {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hl : lookup r n = some f) (ht : targetOf r n = some v) :
    ∀ k, v k ≠ none → k ∈ f.comp.spec := by
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
    rw [hv] at hk
    by_cases hmem : k ∈ f.comp.spec
    · exact hmem
    · simp [hmem] at hk

/-- The target view names only fibers that provision the key, assuming
the table-to-provision invariant. -/
theorem viewProv_target {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hn : NodupKeys r)
    (htableProv : ∀ n f, lookup r n = some f → ∀ k, (f.table k).isSome → k ∈ f.comp.prov)
    (hl : lookup r n = some f) (ht : targetOf r n = some v) :
    ∀ k m, v k = some m → ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov := by
  intro k m hvm
  have hk_spec : k ∈ f.comp.spec :=
    viewSpec_target hl ht k (by rw [hvm]; intro hnone; simp at hnone)
  have htv : v k = providerOf r k := targetOf_view_eq hl ht k hk_spec
  have hprov : providerOf r k = some m := by
    rw [htv] at hvm
    exact hvm
  rcases providerOf_some_lookup_active_table hn hprov with ⟨g, hg, κ, vg, hlcg, htbl⟩
  refine ⟨g, hg, ?_⟩
  exact htableProv m g hg k htbl

/-! ## Pointwise preservation helpers -/

/-- `viewSpec` is preserved by a pointwise update that keeps the component
and the committed view, and does not newly install the fiber. -/
theorem viewSpec_set_viewSame (hvs : ViewSpec r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hinst : new.lc.installed → old.lc.installed)
    (hview : ∀ k, new.lc.viewOf k = old.lc.viewOf k) :
    ViewSpec (set r n new) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    have hold : old.lc.installed := hinst hinst_m
    have hk_ne_old : old.lc.viewOf k ≠ none := by
      rw [hview k] at hk_ne
      exact hk_ne
    have hs := hvs n old h hold k hk_ne_old
    simpa [hc] using hs
  · exact hvs m g hg hinst_m k hk_ne

/-- `tableProv` is preserved by a pointwise update that keeps the table. -/
theorem tableProv_set_viewSame (htp : TableProv r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (htable : ∀ k, new.table k = old.table k) :
    TableProv (set r n new) := by
  intro m g hm k ht
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    have ht_old : (old.table k).isSome := by
      rw [htable k] at ht
      exact ht
    have hp := htp n old h k ht_old
    simpa [hc] using hp
  · exact htp m g hg k ht

/-- `tableProv` is preserved when the new table is a `splitTable` of the
acting fiber's provision.  This is the faithful-model analogue of the old
`tableProv_set_table_step`: `Step.psi` writes `splitTable prov δ.2`, so
every installed table key is already in the provision. -/
theorem tableProv_set_table_split (htp : TableProv r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    {δ : Ctx K V} (htable : ∀ k, new.table k = splitTable old.comp.prov δ.2 k) :
    TableProv (set r n new) := by
  intro m g hm k ht
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    have ht_delta : (splitTable old.comp.prov δ.2 k).isSome := by
      rw [htable k] at ht
      exact ht
    unfold splitTable at ht_delta
    by_cases hk : k ∈ old.comp.prov
    · simpa [hc, hk] using hk
    · simp [hk] at ht_delta
  · exact htp m g hg k ht

/-- `viewProv` is preserved by a pointwise update that keeps the component
and the committed view, and does not newly install the fiber. -/
theorem viewProv_set_viewSame (hvp : ViewProv r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hinst : new.lc.installed → old.lc.installed)
    (hview : ∀ k, new.lc.viewOf k = old.lc.viewOf k) :
    ViewProv (set r n new) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    have hold : old.lc.installed := hinst hinst_m
    have hv_old : old.lc.viewOf k = some p := by
      rw [hview k] at hvm
      exact hvm
    rcases hvp n old h hold k p hv_old with ⟨q, hq, hqprov⟩
    by_cases hpn : p = n
    · subst p
      have hq_old : q = old := Option.some.inj (hq.symm.trans h)
      have hk_old_prov : k ∈ old.comp.prov := by
        rw [hq_old] at hqprov
        exact hqprov
      have hk_new_prov : k ∈ new.comp.prov := by simpa [hc] using hk_old_prov
      exact ⟨new, by simp [lookup_set_eq], hk_new_prov⟩
    · rw [lookup_set_ne r n p new hpn]
      exact ⟨q, hq, hqprov⟩
  · rcases hvp m g hg hinst_m k p hvm with ⟨q, hq, hqprov⟩
    by_cases hpn : p = n
    · subst p
      have hq_old : q = old := Option.some.inj (hq.symm.trans h)
      have hk_old_prov : k ∈ old.comp.prov := by
        rw [hq_old] at hqprov
        exact hqprov
      have hk_new_prov : k ∈ new.comp.prov := by simpa [hc] using hk_old_prov
      exact ⟨new, by simp [lookup_set_eq], hk_new_prov⟩
    · rw [lookup_set_ne r n p new hpn]
      exact ⟨q, hq, hqprov⟩

/-- `viewSpec` is preserved by inserting a fresh inactive fiber. -/
theorem viewSpec_setFresh (hvs : ViewSpec r) {n : N} {fresh : Fiber N K V E}
    (hfresh : fresh.lc = .inactive none) : ViewSpec (set r n fresh) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    rw [hfresh] at hinst_m
    cases hinst_m
  · exact hvs m g hg hinst_m k hk_ne

/-- `viewSpec` is preserved by removal. -/
theorem viewSpec_del (hvs : ViewSpec r) {n : N} : ViewSpec (del r n) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_del_cases (n := n) hm with ⟨hmn, hg⟩
  exact hvs m g hg hinst_m k hk_ne

/-- `viewSpec` is preserved by `L-Begin`. -/
theorem viewSpec_lBegin (hvs : ViewSpec r) {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hf : lookup r n = some f) (ht : targetOf r n = some v) :
    ViewSpec (set r n { f with lc := .loading f.comp.iter id v }) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    change v k ≠ none at hk_ne
    have hk_spec : k ∈ f.comp.spec := viewSpec_target hf ht k hk_ne
    simpa using hk_spec
  · exact hvs m g hg hinst_m k hk_ne

/-- `viewSpec` is preserved by `L-Unload`. -/
theorem viewSpec_lUnload (hvs : ViewSpec r) {n : N} {f : Fiber N K V E}
    {o : Option E} (_hf : lookup r n = some f) :
    ViewSpec (set r n { f with lc := .inactive o }) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    cases hinst_m
  · exact hvs m g hg hinst_m k hk_ne

/-- `viewSpec` is preserved by an unload that writes an arbitrary final
table. -/
theorem viewSpec_lUnload' (hvs : ViewSpec r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    {o : Option E} (hnew : new.lc = .inactive o) :
    ViewSpec (set r n new) := by
  intro m g hm hinst_m k hk_ne
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    rw [hnew] at hinst_m
    cases hinst_m
  · exact hvs m g hg hinst_m k hk_ne

/-- `tableProv` is preserved by inserting a fiber with an empty table. -/
theorem tableProv_setFresh (htp : TableProv r) {n : N} {fresh : Fiber N K V E}
    (hfresh_table : ∀ k, fresh.table k = none) : TableProv (set r n fresh) := by
  intro m g hm k ht
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    rw [hfresh_table k] at ht
    cases ht
  · exact htp m g hg k ht

/-- `tableProv` is preserved by removal. -/
theorem tableProv_del (htp : TableProv r) {n : N} : TableProv (del r n) := by
  intro m g hm k ht
  rcases lookup_del_cases (n := n) hm with ⟨hmn, hg⟩
  exact htp m g hg k ht

/-- `viewProv` is preserved by inserting a fresh inactive fiber. -/
theorem viewProv_setFresh (hvp : ViewProv r) {n : N} {fresh : Fiber N K V E}
    (hnone : lookup r n = none) (hfresh : fresh.lc = .inactive none) :
    ViewProv (set r n fresh) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    rw [hfresh] at hinst_m
    cases hinst_m
  · rcases hvp m g hg hinst_m k p hvm with ⟨q, hq, hqprov⟩
    by_cases hpn : p = n
    · subst p
      rw [hnone] at hq
      simp at hq
    · rw [lookup_set_ne r n p fresh hpn]
      exact ⟨q, hq, hqprov⟩

/-- `viewProv` is preserved by removal. -/
theorem viewProv_del (hwf : WellFormed r) (hvs : ViewSpec r) (hvp : ViewProv r)
    {n : N} {f : Fiber N K V E} {o : Option E}
    (h : lookup r n = some f) (hl : f.lc = .inactive o) :
    ViewProv (del r n) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_del_cases (n := n) hm with ⟨hmn, hg⟩
  rcases hvp m g hg hinst_m k p hvm with ⟨q, hq, hqprov⟩
  have hpn : p ≠ n := by
    intro heq; subst p
    have hk_spec : k ∈ g.comp.spec := hvs m g hg hinst_m k (by
      intro hnone; rw [hnone] at hvm; simp at hvm)
    rcases hwf.viewInstalled m g hg hinst_m k hk_spec n hvm with ⟨gn, hgn, hgninst⟩
    have hgn_f : gn = f := Option.some.inj (hgn.symm.trans h)
    rw [hgn_f, hl] at hgninst
    cases hgninst
  rw [lookup_del_ne (n := n) (m := p) hpn]
  exact ⟨q, hq, hqprov⟩

/-- `viewProv` is preserved by `L-Begin`. -/
theorem viewProv_lBegin (hn : NodupKeys r) (htp : TableProv r) (hvp : ViewProv r)
    {n : N} {f : Fiber N K V E} {v : K → Option N}
    (hf : lookup r n = some f) (_hl : f.lc = .inactive none) (ht : targetOf r n = some v) :
    ViewProv (set r n { f with lc := .loading f.comp.iter id v }) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    change v k = some p at hvm
    rcases viewProv_target hn htp hf ht k p hvm with ⟨q, hq, hqprov⟩
    by_cases hpn : p = n
    · subst p
      have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
      have hk_f_prov : k ∈ f.comp.prov := by rw [hq_f] at hqprov; exact hqprov
      exact ⟨{ f with lc := .loading f.comp.iter id v }, by simp [lookup_set_eq], by simpa using hk_f_prov⟩
    · rw [lookup_set_ne r n p { f with lc := .loading f.comp.iter id v } hpn]
      exact ⟨q, hq, hqprov⟩
  · rcases hvp m g hg hinst_m k p hvm with ⟨q, hq, hqprov⟩
    by_cases hpn : p = n
    · subst p
      have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
      have hk_f_prov : k ∈ f.comp.prov := by rw [hq_f] at hqprov; exact hqprov
      exact ⟨{ f with lc := .loading f.comp.iter id v }, by simp [lookup_set_eq], by simpa using hk_f_prov⟩
    · rw [lookup_set_ne r n p { f with lc := .loading f.comp.iter id v } hpn]
      exact ⟨q, hq, hqprov⟩

/-- `viewProv` is preserved by `L-Unload`. -/
theorem viewProv_lUnload (hvp : ViewProv r) {n : N} {f : Fiber N K V E}
    {o : Option E} (_hf : lookup r n = some f) (hg : ¬ relied r n) :
    ViewProv (set r n { f with lc := .inactive o }) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
  · subst m; subst g
    cases hinst_m
  · rcases hvp m g hg' hinst_m k p hvm with ⟨q, hq, hqprov⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      exact hg ⟨m, k, g, hg', hmn, hinst_m, hvm⟩
    rw [lookup_set_ne r n p { f with lc := .inactive o } hpn]
    exact ⟨q, hq, hqprov⟩

/-! ## Lifecycle-step relations for the current faithful model -/

/-- A lifecycle step in the current faithful model: a `Step` whose kind is
one of the `L-*` rules, together with its `Step.next` target state. -/
def LstepT (s t : State N K E V) : Prop :=
  ∃ st : Step s, Step.IsLifecycle st ∧ Step.next st = t

/-- Lifecycle-only traces of the current faithful table-aware calculus. -/
inductive LTraceT : State N K E V → State N K E V → Prop
  | nil (s : State N K E V) : LTraceT s s
  | cons {s₁ s₂ s₃ : State N K E V} : LstepT s₁ s₂ → LTraceT s₂ s₃ → LTraceT s₁ s₃

/-- `viewProv` is preserved by an unload that writes an arbitrary final
table. -/
theorem viewProv_lUnload' (hvp : ViewProv r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    {o : Option E} (hnew : new.lc = .inactive o) (hg : ¬ relied r n) :
    ViewProv (set r n new) := by
  intro m g hm hinst_m k p hvm
  rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
  · subst m; subst g
    rw [hnew] at hinst_m
    cases hinst_m
  · rcases hvp m g hg' hinst_m k p hvm with ⟨q, hq, hqprov⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      exact hg ⟨m, k, g, hg', hmn, hinst_m, hvm⟩
    rw [lookup_set_ne r n p new hpn]
    exact ⟨q, hq, hqprov⟩

/-! ## Core confined well-formedness and preservation -/

namespace TableConfined

/-- The invariant package needed for table-confined traces.  It is the old
`ConfinedWellFormed` plus the loading-reachability invariant required by the
current faithful `Step` constructors.  It deliberately does **not** include
`InactiveTableEmpty`, because `L-Unload` writes a final table and therefore
does not preserve that progress-only side condition. -/
structure ConfinedWellFormed (r : Registry N K V E) : Prop where
  wf : WellFormed r
  viewSpec : ViewSpec r
  tableProv : TableProv r
  viewProv : ViewProv r
  loadingReach : ReachableLoading r

/-- `viewSpec` is preserved by every current lifecycle step. -/
theorem viewSpec_preserved_lstepT {s t : State N K E V}
    (hvs : ViewSpec s.reg) (hstep : LstepT s t) : ViewSpec t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  cases st with
  | lBegin n f v hf hl ht htable =>
      have hreg : (Step.next (Step.lBegin n f v hf hl ht htable)).reg =
          set s.reg n { f with lc := .loading f.comp.iter id v } := by
        simp [Step.next, Step.psi, Step.edit, hf]
      rw [hreg]
      exact viewSpec_lBegin hvs hf ht
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hreg : (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hreg : (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      have hreg : (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hreg : (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lLeave n f κ v hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewSpec_set_viewSame (old := f) (new := new) hvs hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hreg : (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewSpec_lUnload' hvs hf rfl (show new.lc = .inactive o by rfl)
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife

/-- `tableProv` is preserved by every current lifecycle step. -/
theorem tableProv_preserved_lstepT {s t : State N K E V}
    (htp : TableProv s.reg) (hstep : LstepT s t) : TableProv t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  cases st with
  | lBegin n f v hf hl ht htable =>
      have hreg : (Step.next (Step.lBegin n f v hf hl ht htable)).reg =
          set s.reg n { f with lc := .loading f.comp.iter id v } := by
        simp [Step.next, Step.psi, Step.edit, hf]
      rw [hreg]
      exact tableProv_set_viewSame htp hf rfl (by intro k; rfl)
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hreg : (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact tableProv_set_table_split htp hf rfl (by intro k; rfl)
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hreg : (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact tableProv_set_table_split htp hf rfl (by intro k; rfl)
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      have hreg : (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact tableProv_set_viewSame htp hf rfl (by intro k; rfl)
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact tableProv_set_viewSame htp hf rfl (by intro k; rfl)
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hreg : (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact tableProv_set_table_split htp hf rfl (by intro k; rfl)
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lLeave n f κ v hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact tableProv_set_viewSame htp hf rfl (by intro k; rfl)
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hreg : (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact tableProv_set_table_split htp hf rfl (by intro k; rfl)
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife

/-- `viewProv` is preserved by every current lifecycle step. -/
theorem viewProv_preserved_lstepT {s t : State N K E V}
    (hwf : WellFormed s.reg) (hvs : ViewSpec s.reg)
    (hvp : ViewProv s.reg) (htp : TableProv s.reg) (hstep : LstepT s t) :
    ViewProv t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  cases st with
  | lBegin n f v hf hl ht htable =>
      have hreg : (Step.next (Step.lBegin n f v hf hl ht htable)).reg =
          set s.reg n { f with lc := .loading f.comp.iter id v } := by
        simp [Step.next, Step.psi, Step.edit, hf]
      rw [hreg]
      exact viewProv_lBegin hwf.nodupKeys htp hvp hf hl ht
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hreg : (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hreg : (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      have hreg : (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hreg : (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lLeave n f κ v hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact viewProv_set_viewSame (old := f) (new := new) hvp hf rfl
        (by intro _; rw [hl]; trivial) (by intro k; rw [hl]; rfl)
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hreg : (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact viewProv_lUnload' hvp hf rfl (show new.lc = .inactive o by rfl) hg
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife

/-- The loading-reachability invariant is preserved by every current
lifecycle step. -/
theorem loadingReach_preserved_lstepT {s t : State N K E V}
    (h : ReachableLoading s.reg) (hstep : LstepT s t) :
    ReachableLoading t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  intro m g ι κ v hm hlc
  cases st with
  | lBegin n f v₀ hf hl ht htable =>
      simp [Step.next, Step.psi, Step.edit, hf] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        injection hlc with hι hκ hv
        rw [← hι]
        exact Iterator.Reachable.self f.comp.iter
      · exact h m g ι κ v hg hlc
  | lIter n f ι₀ κ₀ v₀ ι' δ hinv hreach hf hl ht hstep =>
      simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
        lookup_set_eq, set_set_eq] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        injection hlc with hι hκ hv
        rw [← hι]
        exact Iterator.Reachable.trans hreach (Iterator.Reachable.step hstep (Iterator.Reachable.self ι'))
      · exact h m g ι κ v hg hlc
  | lFinish n f ι₀ κ₀ v₀ δ hinv hreach hf hl ht hstep =>
      simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
        lookup_set_eq, set_set_eq] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | lRaise n f ι₀ κ₀ v₀ e hreach hf hl hstep =>
      simp [Step.next, Step.psi, Step.edit, hf] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | lDivertAbort n f ι₀ κ₀ v₀ hreach hf hl ht =>
      simp [Step.next, Step.psi, Step.edit, hf] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | lDivertLand n f ι₀ κ₀ v₀ δ hinv c hreach hf hl ht hstep =>
      simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
        lookup_set_eq, set_set_eq] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | lLeave n f κ₀ v₀ hf hl ht =>
      simp [Step.next, Step.psi, Step.edit, hf] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | lUnload n f κ₀ v₀ o hf hl hg =>
      simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
        lookup_set_eq, set_set_eq] at hm
      rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
      · subst m; subst g
        cases hlc
      · exact h m g ι κ v hg hlc
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife

/-- `TableConfined.ConfinedWellFormed` is preserved by every current
lifecycle step. -/
theorem ConfinedWellFormed.preserved {s t : State N K E V}
    (h : ConfinedWellFormed s.reg) (hstep : LstepT s t) :
    ConfinedWellFormed t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  let hstep' : LstepT s (Step.next st) := ⟨st, hlife, rfl⟩
  constructor
  · exact WellFormed.preserved st h.wf
  · exact viewSpec_preserved_lstepT h.viewSpec hstep'
  · exact tableProv_preserved_lstepT h.tableProv hstep'
  · exact viewProv_preserved_lstepT h.wf h.viewSpec h.viewProv h.tableProv hstep'
  · exact loadingReach_preserved_lstepT h.loadingReach hstep'

/-- `TableConfined.ConfinedWellFormed` is preserved along table-aware
lifecycle traces. -/
theorem ConfinedWellFormed.trace_preserved {s t : State N K E V}
    (h : ConfinedWellFormed s.reg) (ht : LTraceT s t) :
    ConfinedWellFormed t.reg := by
  induction ht with
  | nil => exact h
  | cons hstep _ ih =>
      exact ih (ConfinedWellFormed.preserved h hstep)

/-- Legacy-name alias: `viewSpec` is preserved by a table-aware lifecycle
step. -/
theorem viewSpec_preserved {s t : State N K E V}
    (hvs : ViewSpec s.reg) (hstep : LstepT s t) : ViewSpec t.reg :=
  viewSpec_preserved_lstepT hvs hstep

/-- Legacy-name alias: `viewSpec` is preserved by a table-aware lifecycle
step. -/
theorem viewSpec_preservedT {s t : State N K E V}
    (hvs : ViewSpec s.reg) (hstep : LstepT s t) : ViewSpec t.reg :=
  viewSpec_preserved_lstepT hvs hstep

/-- Legacy-name alias: `tableProv` is preserved by a table-aware lifecycle
step. -/
theorem tableProv_preserved {s t : State N K E V}
    (htp : TableProv s.reg) (hstep : LstepT s t) : TableProv t.reg :=
  tableProv_preserved_lstepT htp hstep

/-- Legacy-name alias: `tableProv` is preserved by a table-aware lifecycle
step. -/
theorem tableProv_preservedT {s t : State N K E V}
    (htp : TableProv s.reg) (hstep : LstepT s t) : TableProv t.reg :=
  tableProv_preserved_lstepT htp hstep

/-- Legacy-name alias: `viewProv` is preserved by a table-aware lifecycle
step. -/
theorem viewProv_preserved {s t : State N K E V}
    (hwf : WellFormed s.reg) (hvs : ViewSpec s.reg)
    (hvp : ViewProv s.reg) (htp : TableProv s.reg) (hstep : LstepT s t) :
    ViewProv t.reg :=
  viewProv_preserved_lstepT hwf hvs hvp htp hstep

/-- Legacy-name alias: `viewProv` is preserved by a table-aware lifecycle
step. -/
theorem viewProv_preservedT {s t : State N K E V}
    (hwf : WellFormed s.reg) (hvs : ViewSpec s.reg)
    (hvp : ViewProv s.reg) (htp : TableProv s.reg) (hstep : LstepT s t) :
    ViewProv t.reg :=
  viewProv_preserved_lstepT hwf hvs hvp htp hstep

end TableConfined

/-! ## Table-confined well-formedness -/

/-- Component table confinement is preserved by a pointwise update that
keeps the component. -/
theorem Registry.TableConfined_set_viewSame (h : Registry.TableConfined r)
    {n : N} {old new : Fiber N K V E} (hf : lookup r n = some old)
    (hc : old.comp = new.comp) : Registry.TableConfined (set r n new) := by
  intro m g hm
  rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
  · subst m; subst g
    rw [← hc]
    exact h n old hf
  · exact h m g hg

/-- `Registry.TableConfined` is preserved by table-aware lifecycle steps. -/
theorem Registry.TableConfined_preserved_lstepT {s t : State N K E V}
    (htconf : Registry.TableConfined s.reg) (hstep : LstepT s t) :
    Registry.TableConfined t.reg := by
  rcases hstep with ⟨st, hlife, hnext⟩
  subst t
  cases st with
  | lBegin n f v hf hl ht htable =>
      have hreg : (Step.next (Step.lBegin n f v hf hl ht htable)).reg =
          set s.reg n { f with lc := .loading f.comp.iter id v } := by
        simp [Step.next, Step.psi, Step.edit, hf]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hreg : (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hreg : (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      have hreg : (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hreg : (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      have hreg : (Step.next (Step.lLeave n f κ v hf hl ht)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hreg : (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
          set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hreg]
      exact Registry.TableConfined_set_viewSame htconf hf rfl
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife

/-- The invariant package for the table-aware calculus. -/
structure TableConfinedWellFormed (r : Registry N K V E) : Prop where
  cwf : TableConfined.ConfinedWellFormed r
  comp : Registry.TableConfined r

/-- `TableConfinedWellFormed` is preserved by table-aware lifecycle steps. -/
theorem TableConfinedWellFormed.preserved_lstepT {s t : State N K E V}
    (h : TableConfinedWellFormed s.reg) (hstep : LstepT s t) :
    TableConfinedWellFormed t.reg := by
  constructor
  · exact TableConfined.ConfinedWellFormed.preserved h.cwf hstep
  · exact Registry.TableConfined_preserved_lstepT h.comp hstep

/-- `TableConfinedWellFormed` is preserved along table-aware lifecycle
traces. -/
theorem TableConfinedWellFormed.ltrace_preservedT {s t : State N K E V}
    (h : TableConfinedWellFormed s.reg) (ht : LTraceT s t) :
    TableConfinedWellFormed t.reg := by
  induction ht with
  | nil => exact h
  | cons hstep _ ih =>
      exact ih (TableConfinedWellFormed.preserved_lstepT h hstep)

/-! ## Table-aware progress and quiescence -/

/-- If an ordinary lifecycle step applies, then a table-aware lifecycle
step applies as well.  In the current model every lifecycle `Step` is
already table-aware, so this is the identity up to `Step.next`. -/
theorem exists_lstepT_of_exists_lstep {s : State N K E V}
    (hstep : ∃ st : Step s, Step.IsLifecycle st) :
    ∃ t : State N K E V, LstepT s t := by
  rcases hstep with ⟨st, hlife⟩
  exact ⟨Step.next st, st, hlife, rfl⟩

/-- **Theorem 66, clause 1 for the table-aware calculus.**  A
non-quiescent, table-confined, acyclic state admits a table-aware
lifecycle step, provided the current-model `InactiveTableEmpty` side
condition holds. -/
theorem exists_lstepT_of_not_quiet {s : State N K E V}
    (h : TableConfinedWellFormed s.reg) (hinactive : InactiveTableEmpty s.reg)
    (hacyc : Acyclic s.reg) (hq : ¬ State.quiet s) :
    ∃ t : State N K E V, LstepT s t := by
  let hcwf : ConfinedWellFormed s.reg :=
    ⟨h.cwf.wf, h.cwf.viewSpec, h.cwf.tableProv, h.cwf.viewProv,
     h.cwf.loadingReach, hinactive⟩
  rcases exists_lifecycle_step_of_not_quiet hcwf hacyc hq with ⟨st, hlife⟩
  exact ⟨Step.next st, st, hlife, rfl⟩

/-- **Quiescence is sound for the table-aware calculus.**  In a quiescent
state no table-aware lifecycle rule applies. -/
theorem no_lstepT_of_quiet {s : State N K E V} (hq : State.quiet s) :
    ¬ ∃ t : State N K E V, LstepT s t := by
  rintro ⟨t, st, hlife, hnext⟩
  exact no_lifecycle_step_of_quiet hq ⟨st, hlife⟩

/-- **Progress and quiescence for the table-aware calculus.**  Under
acyclicity, table-confinement, and the current-model inactive-table side
condition, a state is quiescent exactly when no table-aware lifecycle step
is possible. -/
theorem lstepT_iff_not_quiet {s : State N K E V}
    (h : TableConfinedWellFormed s.reg) (hinactive : InactiveTableEmpty s.reg)
    (hacyc : Acyclic s.reg) :
    (∃ t : State N K E V, LstepT s t) ↔ ¬ State.quiet s := by
  constructor
  · intro ht hq
    exact no_lstepT_of_quiet hq ht
  · intro hq
    exact exists_lstepT_of_not_quiet h hinactive hacyc hq

/-- **Maximal finite table-aware traces end in quiescence.**  The
current-model `InactiveTableEmpty` side condition is included at the end
state because `L-Unload` does not preserve it. -/
theorem maximal_ltrace_ends_quiet {s t : State N K E V}
    (h : TableConfinedWellFormed s.reg) (ht : LTraceT s t)
    (hinactive' : InactiveTableEmpty t.reg) (hacyc' : Acyclic t.reg)
    (hmax : ¬ ∃ u : State N K E V, LstepT t u) : State.quiet t := by
  have h' : TableConfinedWellFormed t.reg := TableConfinedWellFormed.ltrace_preservedT h ht
  apply Classical.byContradiction
  intro hq
  exact hmax (exists_lstepT_of_not_quiet h' hinactive' hacyc' hq)

end Cordix
