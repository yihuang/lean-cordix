import LeanCordix.WellFormed
import LeanCordix.Step

/-!
# LeanCordix.Progress — Theorem 66.1 (Progress) scaffolding

This module ports the progress part of deleted Theorem 66 onto the current
faithful full-context model.

It provides:

* `Precedes` / `Acyclic` (Definition 65);
* state-level wrappers `State.Precedes` / `State.Acyclic`;
* the confinement-derived invariants (`ViewSpec`, `ViewProv`, `TableProv`)
  together with the two invariants that the current `Step` constructors
  additionally need (`ReachableLoading`, `InactiveTableEmpty`);
* `exists_lifecycle_step_or_guarded` — no deadlock except a guarded unload;
* `no_guarded_unload_of_acyclic` — acyclicity eliminates the guarded unload;
* `exists_lifecycle_step_of_not_quiet` — Theorem 66, clause 1;
* `no_lifecycle_step_of_quiet` — quiescence admits no lifecycle step.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

open Classical

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

namespace State

/-- **Definition 65 at the state level.** -/
def Precedes (s : State N K E V) (n m : N) : Prop :=
  Cordix.Precedes s.reg n m

/-- Acyclicity at the state level. -/
def Acyclic (s : State N K E V) : Prop :=
  Cordix.Acyclic s.reg

end State

/-! ## Confinement-derived and step-constructor invariants -/

/-- Installed committed views only name declared keys. -/
def ViewSpec (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k, f.lc.viewOf k ≠ none → k ∈ f.comp.spec

/-- Installed committed views name only fibers whose provision contains
that key. -/
def ViewProv (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k m, f.lc.viewOf k = some m →
    ∃ g, lookup r m = some g ∧ k ∈ g.comp.prov

/-- Every table key is in the fiber's provision. -/
def TableProv (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f →
    ∀ k, (f.table k).isSome → k ∈ f.comp.prov

/-- The current faithful `Step` constructors require a reachability proof
for a loading iterator.  Real traces preserve this invariant, but it is not
recorded in `Fiber`/`Lifecycle`, so the state-level progress theorem takes it
as an explicit side condition. -/
def ReachableLoading (r : Registry N K V E) : Prop :=
  ∀ n f ι κ v, lookup r n = some f → f.lc = .loading ι κ v →
    Iterator.Reachable f.comp.iter ι

/-- The current faithful `L-Begin` rule additionally requires the inactive
fiber's table to be empty. -/
def InactiveTableEmpty (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → f.lc = .inactive none →
    f.table = fun _ => none

/-- The confinement-derived invariants plus the two current-model side
conditions needed for the acyclic progress theorem. -/
structure ConfinedWellFormed (r : Registry N K V E) : Prop where
  wf : WellFormed r
  viewSpec : ViewSpec r
  tableProv : TableProv r
  viewProv : ViewProv r
  reachableLoading : ReachableLoading r
  inactiveTableEmpty : InactiveTableEmpty r

namespace Step

/-- A step is a lifecycle step when its kind is one of the `L-*` rules. -/
def IsLifecycle {s : State N K E V} (st : Step s) : Prop :=
  Full.StepKind.isLifecycle st.kind

end Step

/-! ## Progress: no deadlock except the guarded unload -/

/-- A loading fiber always has a lifecycle step, given the reachability
invariant required by the current `Step` constructors. -/
theorem exists_lifecycle_step_of_loading {s : State N K E V}
    (hreach : ReachableLoading s.reg)
    {m : N} {g : Fiber N K V E} {ι : Iterator (Ctx K V) E}
    {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hg : lookup s.reg m = some g) (hlc : g.lc = .loading ι κ v) :
    ∃ st : Step s, Step.IsLifecycle st := by
  have hR : Iterator.Reachable g.comp.iter ι := hreach m g ι κ v hg hlc
  by_cases ht : State.targetOf s m = some v
  · cases hstep : Iterator.step ι (State.fullCtx s) with
    | error e =>
        exact ⟨Step.lRaise m g ι κ v e hR hg hlc hstep,
          by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩
    | ok p =>
        rcases p with ⟨δ, h, c⟩
        cases c with
        | none =>
            exact ⟨Step.lFinish m g ι κ v δ h hR hg hlc ht hstep,
              by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩
        | some ι' =>
            exact ⟨Step.lIter m g ι κ v ι' δ h hR hg hlc ht hstep,
              by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩
  · exact ⟨Step.lDivertAbort m g ι κ v hR hg hlc ht,
      by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩

/-- If no lifecycle step and no guarded unload exist, the state must be
quiescent.  This is the contrapositive used to prove
`exists_lifecycle_step_or_guarded`. -/
theorem quiet_of_no_lifecycle_step_or_guarded {s : State N K E V}
    (hreach : ReachableLoading s.reg) (hinactive : InactiveTableEmpty s.reg)
    (hno : ¬ ((∃ st : Step s, Step.IsLifecycle st) ∨
      (∃ n f κ v o, lookup s.reg n = some f ∧ f.lc = .unloading κ v o ∧ State.relied s n))) :
    State.quiet s := by
  intro n f hl
  cases hlc : f.lc with
  | inactive o =>
      by_cases ho : o = none
      · subst o
        by_cases ht : targetOf s.reg n = none
        · exact Or.inr ht
        · cases ht' : targetOf s.reg n with
          | none => exact absurd ht' ht
          | some v =>
              have htable : f.table = fun _ => none := hinactive n f hl hlc
              have hstep : ∃ st : Step s, Step.IsLifecycle st :=
                ⟨Step.lBegin n f v hl hlc ht' htable,
                  by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩
              exact False.elim (hno (Or.inl hstep))
      · exact Or.inl ho
  | loading ι κ v =>
      exfalso
      exact hno (Or.inl (exists_lifecycle_step_of_loading hreach hl hlc))
  | active κ v =>
      by_cases ht : targetOf s.reg n = some v
      · exact ht
      · exfalso
        exact hno (Or.inl ⟨Step.lLeave n f κ v hl hlc ht,
          by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩)
  | unloading κ v o =>
      by_cases hrel : State.relied s n
      · exfalso
        exact hno (Or.inr ⟨n, f, κ, v, o, hl, hlc, hrel⟩)
      · exfalso
        exact hno (Or.inl ⟨Step.lUnload n f κ v o hl hlc hrel,
          by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩)

/-- **Theorem 66, clause 1 (full calculus).** A non-quiescent state either
admits a lifecycle step, or has a fiber in `unloading` whose guard
(`relied`) is still closed.  With the acyclicity hypothesis of the paper the
second case is impossible; here we make the disjunction explicit. -/
theorem exists_lifecycle_step_or_guarded {s : State N K E V}
    (hreach : ReachableLoading s.reg) (hinactive : InactiveTableEmpty s.reg)
    (h : ¬ State.quiet s) :
    (∃ st : Step s, Step.IsLifecycle st) ∨
    (∃ n f κ v o, lookup s.reg n = some f ∧ f.lc = .unloading κ v o ∧ State.relied s n) := by
  apply Classical.byContradiction
  intro hno
  exact h (quiet_of_no_lifecycle_step_or_guarded hreach hinactive hno)

/-- An active fiber whose target equals its committed view cannot have a
committed view naming a fiber that is unloading: the provider of the key
would have to be both active and unloading. -/
theorem active_view_unload_false {r : Registry N K V E} (hwf : WellFormed r)
    (hviewSpec : ViewSpec r)
    {m : N} {g : Fiber N K V E} {κg : Ctx K V → Ctx K V}
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
theorem next_guarded_of_guarded {s : State N K E V} (hwf : WellFormed s.reg)
    (hviewSpec : ViewSpec s.reg) (hviewProv : ViewProv s.reg)
    (hreach : ReachableLoading s.reg)
    (hno : ¬ ∃ st : Step s, Step.IsLifecycle st)
    {n : N} {f : Fiber N K V E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {o : Option E}
    (hlook_n : lookup s.reg n = some f) (hlc_n : f.lc = .unloading κ v o)
    (hrel : State.relied s n) :
    ∃ m g κ' v' o', lookup s.reg m = some g ∧ g.lc = .unloading κ' v' o'
      ∧ State.relied s m ∧ Precedes s.reg n m := by
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
      exact hno (exists_lifecycle_step_of_loading hreach hg hlc_m)
  | active κg vg =>
      by_cases ht : State.targetOf s m = some vg
      · exfalso
        exact active_view_unload_false hwf hviewSpec hg hlc_m ht hv_mk hlook_n hlc_n
      · exfalso
        exact hno ⟨Step.lLeave m g κg vg hg hlc_m ht,
          by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩
  | unloading κg vg og =>
      by_cases hrel_m : State.relied s m
      · refine ⟨m, g, κg, vg, og, hg, hlc_m, hrel_m, ?_⟩
        rcases hviewProv m g hg hinst_m k n hv_mk with ⟨gn, hgn, hk_prov⟩
        have hgn_f : gn = f := Option.some.inj (hgn.symm.trans hlook_n)
        have hk_prov_f : k ∈ f.comp.prov := by
          rw [hgn_f] at hk_prov
          exact hk_prov
        exact ⟨f, g, hlook_n, hg, k, hk_prov_f, hk_spec⟩
      · exfalso
        exact hno ⟨Step.lUnload m g κg vg og hg hlc_m hrel_m,
          by simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle]⟩

/-- Under acyclicity, the guarded-unload disjunct is impossible. -/
theorem no_guarded_unload_of_acyclic {s : State N K E V} (hwf : WellFormed s.reg)
    (hacyc : Acyclic s.reg)
    (hviewSpec : ViewSpec s.reg) (hviewProv : ViewProv s.reg)
    (hreach : ReachableLoading s.reg)
    (hno : ¬ ∃ st : Step s, Step.IsLifecycle st) :
    ∀ n f κ v o, lookup s.reg n = some f → f.lc = .unloading κ v o → ¬ State.relied s n := by
  intro n
  refine @WellFounded.induction N (fun a b : N => Precedes s.reg b a) hacyc
    (fun n => ∀ f κ v o, lookup s.reg n = some f → f.lc = .unloading κ v o → ¬ State.relied s n) n ?_
  intro x ih f κ v o hlook_n hlc_n hrel
  rcases next_guarded_of_guarded hwf hviewSpec hviewProv hreach hno hlook_n hlc_n hrel
    with ⟨m, g, κ', v', o', hg, hlc_m, hrel_m, hprec⟩
  have hprecR : (fun a b : N => Precedes s.reg b a) m x := hprec
  have hC_m := ih m hprecR g κ' v' o' hg hlc_m
  exact hC_m hrel_m

/-- **Theorem 66, clause 1 (faithful full-context form).**  Under acyclic
precedence, the confinement-derived view invariants, and the two side
conditions required by the current `Step` constructors, a non-quiescent
state admits a lifecycle step. -/
theorem exists_lifecycle_step_of_not_quiet_of_acyclic {s : State N K E V}
    (hwf : WellFormed s.reg) (hacyc : Acyclic s.reg)
    (hviewSpec : ViewSpec s.reg) (hviewProv : ViewProv s.reg)
    (hreach : ReachableLoading s.reg) (hinactive : InactiveTableEmpty s.reg)
    (h : ¬ State.quiet s) : ∃ st : Step s, Step.IsLifecycle st := by
  apply Classical.byContradiction
  intro hno
  rcases exists_lifecycle_step_or_guarded hreach hinactive h with hstep | hguard
  · exact hno hstep
  · rcases hguard with ⟨n, f, κ, v, o, hf, hl, hr⟩
    exact (no_guarded_unload_of_acyclic hwf hacyc hviewSpec hviewProv hreach hno n f κ v o hf hl) hr

/-- **Theorem 66, clause 1 (packaged).**  `ConfinedWellFormed` bundles the
confinement-derived invariants and the current-model side conditions. -/
theorem exists_lifecycle_step_of_not_quiet {s : State N K E V}
    (hcwf : ConfinedWellFormed s.reg) (hacyc : Acyclic s.reg)
    (h : ¬ State.quiet s) : ∃ st : Step s, Step.IsLifecycle st :=
  exists_lifecycle_step_of_not_quiet_of_acyclic hcwf.wf hacyc hcwf.viewSpec hcwf.viewProv
    hcwf.reachableLoading hcwf.inactiveTableEmpty h

/-! ## Quiescence and the absence of lifecycle steps -/

/-- **Quiescence is sound.**  In a quiescent state no lifecycle rule
applies. -/
theorem no_lifecycle_step_of_quiet {s : State N K E V} (hq : State.quiet s) :
    ¬ ∃ st : Step s, Step.IsLifecycle st := by
  rintro ⟨st, hlife⟩
  cases st with
  | oInsert n c p hn hp hdisj =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRetire n f hf =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | oRemove n f o hf hl hchild =>
      simp [Step.IsLifecycle, Step.kind, Full.StepKind.isLifecycle] at hlife
  | lBegin n f v hf hl ht htable =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
      rw [hq'] at ht
      simp at ht
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lRaise n f ι κ v e hreach hf hl hstep =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      have hq' := hq n f hf
      rw [hl] at hq'
      simp at hq'
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
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

end Cordix
