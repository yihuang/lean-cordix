import LeanCordix.Trace

/-!
# LeanCordix.Coherence — Theorem 64 (Resolution coherence)

This module ports the resolution-coherence part of Theorem 64 from the
deleted legacy `Global.lean` onto the current faithful full-context model.
It formalises the loading/unloading lifecycle dichotomy and shows that, in a
trace whose steps on a fiber `n` are only `L-Iter`/`L-Finish`, the committed
view `v` is fixed throughout and every such step runs against exactly that
one resolution `v`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

namespace StepTrace

/-- A type-level trace predicate: the committed view of `n` is `v` at the
source of every step in the trace and at that step's next state. -/
def ViewFixedAlong {s t : State N K E V} (n : N) (v : K → Option N) :
    StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      (st.name ≠ n ∨
        (∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v ∧
              ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v)) ∧
      ViewFixedAlong n v ht

end StepTrace

namespace Step

/-- **Theorem 64, loading-step dichotomy.**  A lifecycle step acting on a
`loading` fiber is one of the five loading rules: `L-Iter`, `L-Finish`,
`L-Raise`, `L-Divert` (abort or landing).  The first two keep the initial
loading interval; the last three leave it. -/
theorem kind_of_loading_lifecycle {s : State N K E V} (st : Step s)
    {n : N} {f : Fiber N K V E} {ι : Iterator (Ctx K V) E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hn : st.name = n)
    (hlife : Full.StepKind.isLifecycle st.kind)
    (hf : lookup s.reg n = some f)
    (hl : f.lc = .loading ι κ v) :
    st.kind = Full.StepKind.lIter ∨ st.kind = Full.StepKind.lFinish ∨
    st.kind = Full.StepKind.lRaise ∨ st.kind = Full.StepKind.lDivertAbort ∨
    st.kind = Full.StepKind.lDivertLand := by
  cases st with
  | lIter n0 f0 ι0 κ0 v0 ι' δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inl rfl
  | lFinish n0 f0 ι0 κ0 v0 δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inr (Or.inl rfl)
  | lRaise n0 f0 ι0 κ0 v0 e hreach hf0 hl0 hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inr (Or.inr (Or.inl rfl))
  | lDivertAbort n0 f0 ι0 κ0 v0 hreach hf0 hl0 ht =>
      simp [Step.name] at hn
      subst n0
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | lDivertLand n0 f0 ι0 κ0 v0 δ h c hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | oInsert n0 c p hn0 hp hdisj =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife
  | oRetire n0 f0 hf0 =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife
  | oRemove n0 f0 o hf0 hl0 hchild =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife
  | lBegin n0 f0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lLeave n0 f0 κ0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lUnload n0 f0 κ0 v0 o hf0 hl0 hg =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0

/-- **Theorem 64, unloading-closing half.**  Once a fiber is `unloading`,
the only lifecycle step that can act on it is `L-Unload`.  This is the
last step that closes an episode after `L-Raise`/`L-Divert`. -/
theorem kind_of_unloading_lifecycle {s : State N K E V} (st : Step s)
    {n : N} {f : Fiber N K V E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {o : Option E}
    (hn : st.name = n)
    (hlife : Full.StepKind.isLifecycle st.kind)
    (hf : lookup s.reg n = some f)
    (hl : f.lc = .unloading κ v o) :
    st.kind = Full.StepKind.lUnload := by
  cases st with
  | lUnload n0 f0 κ0 v0 o0 hf0 hl0 hg =>
      simp [Step.name] at hn
      subst n0
      rfl
  | lBegin n0 f0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lIter n0 f0 ι0 κ0 v0 ι' δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lFinish n0 f0 ι0 κ0 v0 δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lRaise n0 f0 ι0 κ0 v0 e hreach hf0 hl0 hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lDivertAbort n0 f0 ι0 κ0 v0 hreach hf0 hl0 ht =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lDivertLand n0 f0 ι0 κ0 v0 δ h c hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lLeave n0 f0 κ0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | oInsert n0 c p hn0 hp hdisj =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife
  | oRetire n0 f0 hf0 =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife
  | oRemove n0 f0 o hf0 hl0 hchild =>
      simp [Step.name, Step.kind, Full.StepKind.isLifecycle] at hn hlife

/-- **Theorem 64, leaving-loading half.**  If a `loading` fiber leaves the
loading interval through `L-Raise`/`L-Divert`, its next lifecycle state is
`unloading` (with the same committed view `v`). -/
theorem next_unloading_of_loading_exit {s : State N K E V} (st : Step s)
    {n : N} {f : Fiber N K V E} {ι : Iterator (Ctx K V) E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hn : st.name = n)
    (hf : lookup s.reg n = some f)
    (hl : f.lc = .loading ι κ v)
    (hexit : st.kind = Full.StepKind.lRaise ∨ st.kind = Full.StepKind.lDivertAbort ∨
              st.kind = Full.StepKind.lDivertLand) :
    ∃ κ' o f', lookup (Step.next st).reg n = some f' ∧ f'.lc = .unloading κ' v o := by
  cases st with
  | lRaise n0 f0 ι0 κ0 v0 e hreach hf0 hl0 hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f0
      have hκ : κ0 = κ := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hκ.symm
      have hv0 : v0 = v := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hv.symm
      refine ⟨κ, some e, { f with lc := .unloading κ v (some e) }, ?_⟩
      simp [Step.next, Step.edit, Step.psi, hf, hκ, hv0, lookup_set_eq]
  | lDivertAbort n0 f0 ι0 κ0 v0 hreach hf0 hl0 ht =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f0
      have hκ : κ0 = κ := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hκ.symm
      have hv0 : v0 = v := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hv.symm
      refine ⟨κ, none, { f with lc := .unloading κ v none }, ?_⟩
      simp [Step.next, Step.edit, Step.psi, hf, hκ, hv0, lookup_set_eq]
  | lDivertLand n0 f0 ι0 κ0 v0 δ h c hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f0
      have hκ : κ0 = κ := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hκ.symm
      have hv0 : v0 = v := by
        rw [hl] at hl0
        injection hl0 with hι hκ hv
        exact hv.symm
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      refine ⟨κ ∘ h, none, new, ?_⟩
      simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
        lookup_set_eq, set_set_eq, hκ, hv0, new]
  | lIter n0 f0 ι0 κ0 v0 ι' δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name, Step.kind] at hn hexit
  | lFinish n0 f0 ι0 κ0 v0 δ h hreach hf0 hl0 ht hstep =>
      simp [Step.name, Step.kind] at hn hexit
  | lBegin n0 f0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lLeave n0 f0 κ0 v0 hf0 hl0 ht0 =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | lUnload n0 f0 κ0 v0 o hf0 hl0 hg =>
      simp [Step.name] at hn
      subst n0
      have hf_eq : f = f0 := Option.some.inj (hf.symm.trans hf0)
      subst f
      rw [hl] at hl0
      simp at hl0
  | oInsert n0 c p hn0 hp hdisj =>
      simp [Step.name, Step.kind] at hn hexit
  | oRetire n0 f0 hf0 =>
      simp [Step.name, Step.kind] at hn hexit
  | oRemove n0 f0 o hf0 hl0 hchild =>
      simp [Step.name, Step.kind] at hn hexit

/-- An `L-Iter` or `L-Finish` step acting on a fiber whose committed view
is `v` preserves that committed view. -/
theorem view_preserved_of_iter {s : State N K E V} (st : Step s)
    {n : N} {v : K → Option N}
    (hn : st.name = n)
    (hk : st.kind = Full.StepKind.lIter ∨ st.kind = Full.StepKind.lFinish)
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v) :
    ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v := by
  cases st with
  | lIter n0 f ι κ v0 ι' δ h hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hstart with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v0 }
      refine ⟨new, ?_, ?_⟩
      · simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      · simp [Lifecycle.viewOf, hv0, new]
  | lFinish n0 f ι κ v0 δ h hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hstart with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v0 }
      refine ⟨new, ?_, ?_⟩
      · simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      · simp [Lifecycle.viewOf, hv0, new]
  | _ =>
      simp [Step.name, Step.kind] at hn hk

/-- An `L-Iter` or `L-Finish` step acting on a fiber whose committed view
is `v` runs against exactly that resolution `v`. -/
theorem target_eq_of_iter_view {s : State N K E V} (st : Step s)
    {n : N} {v : K → Option N}
    (hn : st.name = n)
    (hk : st.kind = Full.StepKind.lIter ∨ st.kind = Full.StepKind.lFinish)
    (hview : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v) :
    State.targetOf s n = some v := by
  cases st with
  | lIter n0 f ι κ v0 ι' δ h hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hview with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      simpa [State.targetOf, hv0] using ht
  | lFinish n0 f ι κ v0 δ h hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hview with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      simpa [State.targetOf, hv0] using ht
  | _ =>
      simp [Step.name, Step.kind] at hn hk

end Step

namespace StepTrace

/-- **Theorem 64, view-fixity half.**  In a trace whose `n`-steps are only
`L-Iter`/`L-Finish`, the committed view of `n` is fixed to `v` throughout. -/
theorem view_fixed_of_iteration_trace {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v)
    (hall : StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ st.kind = Full.StepKind.lIter ∨ st.kind = Full.StepKind.lFinish) ht) :
    StepTrace.ViewFixedAlong n v ht := by
  induction ht with
  | nil s => trivial
  | cons st hnext ht ih =>
      rcases hall with ⟨hst, htail⟩
      constructor
      · by_cases hn : st.name = n
        · right
          rcases hst with hne | hk
          · exact False.elim (hne hn)
          · rcases hstart with ⟨f, hf, hv⟩
            rcases Step.view_preserved_of_iter st hn hk ⟨f, hf, hv⟩ with ⟨f', hf', hv'⟩
            exact ⟨f, hf, hv, f', hf', hv'⟩
        · left
          exact hn
      · have hstart' : ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v := by
          by_cases hn : st.name = n
          · rcases hst with hne | hk
            · exact False.elim (hne hn)
            · rcases hstart with ⟨f, hf, hv⟩
              exact Step.view_preserved_of_iter st hn hk ⟨f, hf, hv⟩
          · rcases hstart with ⟨f, hf, hv⟩
            have hne' : n ≠ st.name := fun h => hn h.symm
            have hf' : lookup (Step.next st).reg n = some f := by
              rw [Step.factorization]
              rw [Step.edit_preserves_lookup_ne st hne']
              rw [Step.psi_preserves_lookup_ne st hne']
              exact hf
            exact ⟨f, hf', hv⟩
        exact ih (by rwa [hnext] at hstart') htail

/-- **Theorem 64, Eq. (59).**  In the initial interval of an episode, every
`L-Iter`/`L-Finish` of the transition runs against the one committed
resolution `v`. -/
theorem resolution_coherent_of_iteration_trace {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v)
    (hall : StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ st.kind = Full.StepKind.lIter ∨ st.kind = Full.StepKind.lFinish) ht) :
    StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ State.targetOf s n = some v) ht := by
  induction ht with
  | nil s => trivial
  | cons st hnext ht ih =>
      rcases hall with ⟨hst, htail⟩
      constructor
      · by_cases hn : st.name = n
        · right
          rcases hst with hne | hk
          · exact False.elim (hne hn)
          · exact Step.target_eq_of_iter_view st hn hk hstart
        · left
          exact hn
      · have hstart' : ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v := by
          by_cases hn : st.name = n
          · rcases hst with hne | hk
            · exact False.elim (hne hn)
            · rcases hstart with ⟨f, hf, hv⟩
              exact Step.view_preserved_of_iter st hn hk ⟨f, hf, hv⟩
          · rcases hstart with ⟨f, hf, hv⟩
            have hne' : n ≠ st.name := fun h => hn h.symm
            have hf' : lookup (Step.next st).reg n = some f := by
              rw [Step.factorization]
              rw [Step.edit_preserves_lookup_ne st hne']
              rw [Step.psi_preserves_lookup_ne st hne']
              exact hf
            exact ⟨f, hf', hv⟩
        exact ih (by rwa [hnext] at hstart') htail

end StepTrace

end Cordix
