import LeanCordix.Invariance

/-!
# Cordix — Section 4.4.2/4.4.3: Recovery exactness and resolution coherence

This module begins the global metatheory that the roadmap calls *recovery
exactness / resolution coherence*.  It introduces the effect-side relation
`State.Approx` (the paper's `≈`: two states agree on the ambient context and
on every fiber's raw table, while control fields such as lifecycle, parent,
retirement, and the registry bookkeeping may differ).  It proves the
`edit`-only control-field preservation lemma for the control-only steps, and
packages it as a first recovery-exactness result for traces whose other
fibers perform no table write, no ambient accumulator application, and no
removal.

It also formalizes the resolution-coherence part of Theorem 64: along a
trace that starts with a committed view `v` and whose steps on the fiber in
question are only `L-Iter`/`L-Finish`, the committed view is fixed and every
iteration in that trace runs against the one resolution `v`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## The effect-side relation `≈` -/

/-- The raw table read from a state at a name; an absent name reads as the
empty table.  This is the table half of the paper's `≈`: control fields are
forgotten, but ambient effects and raw tables are compared exactly. -/
def State.tableAt (s : State N K E V) (n : N) : CoefCtx K V :=
  match lookup s.reg n with
  | some f => f.table
  | none => fun _ => none

/-- **The paper's `≈`.** Two states agree on everything but the control
fields: the ambient context is equal and every name's raw table is equal
(an absent name is the same as an empty table). -/
structure State.Approx (s s' : State N K E V) : Prop where
  ambient : s.ambient = s'.ambient
  tables : ∀ n, State.tableAt s n = State.tableAt s' n

namespace State.Approx

theorem refl (s : State N K E V) : State.Approx s s := ⟨rfl, fun _ => rfl⟩

theorem symm {s s' : State N K E V} (h : State.Approx s s') : State.Approx s' s :=
  ⟨h.ambient.symm, fun n => (h.tables n).symm⟩

theorem trans {s s' s'' : State N K E V} (h : State.Approx s s')
    (h' : State.Approx s' s'') : State.Approx s s'' :=
  ⟨h.ambient.trans h'.ambient, fun n => (h.tables n).trans (h'.tables n)⟩

end State.Approx

/-- `tableAt` after a pointwise `set` at the updated name. -/
theorem State.tableAt_set_eq (r : Registry N K V E) (n : N) (g : Fiber N K V E)
    (a : CoefCtx K V) :
    State.tableAt ⟨set r n g, a⟩ n = g.table := by
  simp [State.tableAt]

/-- `tableAt` after a pointwise `set` away from the updated name. -/
theorem State.tableAt_set_ne (r : Registry N K V E) (n m : N) (g : Fiber N K V E)
    (a : CoefCtx K V) (hmn : m ≠ n) :
    State.tableAt ⟨set r n g, a⟩ m = State.tableAt ⟨r, a⟩ m := by
  simp [State.tableAt, lookup_set_ne r n m g hmn]

/-- The table-writing part of a `Ψ`: replace the raw table at `n` by `δ`,
or do nothing when `n` is absent. -/
def State.writeTable (s : State N K E V) (n : N) (δ : CoefCtx K V) : State N K E V :=
  match lookup s.reg n with
  | some g => ⟨set s.reg n { g with table := δ }, s.ambient⟩
  | none => s

/-- A table-writing `Ψ` preserves `≈` when the acting name is present in
both states or absent from both states. -/
theorem State.writeTable_preserves_approx {x y : State N K E V}
    (h : State.Approx x y) {n : N} {δ : CoefCtx K V}
    (hdom : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome) :
    State.Approx (State.writeTable x n δ) (State.writeTable y n δ) := by
  constructor
  · unfold State.writeTable
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      simp [hfx, hfy, h.ambient]
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [hxn, hyn, h.ambient]
  · intro m
    unfold State.writeTable
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      by_cases hmn : m = n
      · subst m
        simp [State.tableAt, hfx, hfy, State.tableAt_set_eq]
      · simp [State.tableAt, hfx, hfy, State.tableAt_set_ne, hmn]
        exact h.tables m
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [State.tableAt, hxn, hyn]
      exact h.tables m

/-- The accumulator carried by a lifecycle state; `id` for inactive. -/
def Lifecycle.acc {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → CoefCtx K V → CoefCtx K V
  | .inactive _ => id
  | .loading _ κ _ => κ
  | .active κ _ => κ
  | .unloading κ _ _ => κ

/-- Apply a fiber's accumulator to the ambient context, leaving all tables
unchanged.  This is the state-level reading of the paper's `κ_n` on the
part of the state that `≈` compares. -/
def State.applyAcc (s : State N K E V) (n : N) : State N K E V :=
  match lookup s.reg n with
  | some f =>
      match f.lc with
      | .inactive _ => s
      | .loading _ κ _ => ⟨s.reg, κ s.ambient⟩
      | .active κ _ => ⟨s.reg, κ s.ambient⟩
      | .unloading κ _ _ => ⟨s.reg, κ s.ambient⟩
  | none => s

/-- Applying the identity accumulator of a freshly begun fiber is the
identity on states. -/
theorem State.applyAcc_of_loading_id {s : State N K E V} {n : N}
    {f : Fiber N K V E} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading f.comp.iter id v) :
    State.applyAcc s n = s := by
  cases f with
  | mk comp parent table retired lc =>
      have hl' : lc = .loading comp.iter id v := by simpa using hl
      simp [State.applyAcc, hf, hl']

/-! ## Control-only edits preserve `≈` -/

/-- A control-only edit is one of the rules whose `Ψ` is the identity and
whose `edit` does not delete a raw table.  In the paper these are exactly
the rows whose writes are confined to control fields. -/
def ControlOnly {s : State N K E V} (st : Step s) : Prop :=
  st.kind ≠ StepKind.lIter ∧ st.kind ≠ StepKind.lFinish ∧
    st.kind ≠ StepKind.lDivertLand ∧ st.kind ≠ StepKind.lUnload ∧
    st.kind ≠ StepKind.oRemove

/-- A control-only step leaves every raw table unchanged. -/
theorem Step.edit_control_tableAt {s : State N K E V} (st : Step s)
    (hno : ControlOnly st) :
    ∀ m, State.tableAt (Step.next st) m = State.tableAt s m := by
  intro m
  cases st with
  | oInsert n c p hn hp hdisj =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, State.tableAt, hn]
      · simp [Step.next, Step.edit, Step.psi, State.tableAt, lookup_set_ne, hmn]
  | oRetire n f hf =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, hf, State.tableAt]
      · simp [Step.next, Step.edit, Step.psi, hf, State.tableAt, lookup_set_ne, hmn]
  | oRemove n f o hf hl hchild =>
      simp [ControlOnly, Step.kind] at hno
  | lBegin n f v hf hl ht =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, hf, State.tableAt]
      · simp [Step.next, Step.edit, Step.psi, hf, State.tableAt, lookup_set_ne, hmn]
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      simp [ControlOnly, Step.kind] at hno
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      simp [ControlOnly, Step.kind] at hno
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, hf, State.tableAt]
      · simp [Step.next, Step.edit, Step.psi, hf, State.tableAt, lookup_set_ne, hmn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, hf, State.tableAt]
      · simp [Step.next, Step.edit, Step.psi, hf, State.tableAt, lookup_set_ne, hmn]
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep =>
      simp [ControlOnly, Step.kind] at hno
  | lLeave n f κ v hf hl ht =>
      by_cases hmn : m = n
      · subst m
        simp [Step.next, Step.edit, Step.psi, hf, State.tableAt]
      · simp [Step.next, Step.edit, Step.psi, hf, State.tableAt, lookup_set_ne, hmn]
  | lUnload n f κ v o hf hl hg =>
      simp [ControlOnly, Step.kind] at hno

/-- A control-only step leaves the ambient context unchanged. -/
theorem Step.edit_control_ambient {s : State N K E V} (st : Step s)
    (hno : ControlOnly st) :
    (Step.next st).ambient = s.ambient := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.next, Step.edit, Step.psi]
  | oRetire n f hf => simp [Step.next, Step.edit, Step.psi, hf]
  | oRemove n f o hf hl hchild => simp [ControlOnly, Step.kind] at hno
  | lBegin n f v hf hl ht => simp [Step.next, Step.edit, Step.psi, hf]
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep => simp [ControlOnly, Step.kind] at hno
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep => simp [ControlOnly, Step.kind] at hno
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.next, Step.edit, Step.psi, hf]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.next, Step.edit, Step.psi, hf]
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep => simp [ControlOnly, Step.kind] at hno
  | lLeave n f κ v hf hl ht => simp [Step.next, Step.edit, Step.psi, hf]
  | lUnload n f κ v o hf hl hg => simp [ControlOnly, Step.kind] at hno

/-- **First half of the recovery-exactness step lemma.**  For the
control-only rules, `edit` writes no effect: `next st ≈ s`. -/
theorem Step.edit_control_preserves_approx {s : State N K E V} (st : Step s)
    (hno : ControlOnly st) :
    State.Approx (Step.next st) s :=
  ⟨Step.edit_control_ambient st hno, Step.edit_control_tableAt st hno⟩

/-- **Every `Ψ` preserves `≈`.**  A step's state map is either the identity,
a fixed table write at its acting name, or the application of a fixed
ambient accumulator at `L-Unload`; each of these carries `≈`-equal states
to `≈`-equal states, provided the acting name has the same presence in the
two input states. -/
theorem Step.psi_preserves_approx {s x y : State N K E V} (st : Step s)
    (h : State.Approx x y)
    (hdom : (lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome) :
    State.Approx (Step.psi st x) (Step.psi st y) := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi] using h
  | oRetire n f hf => simpa [Step.psi] using h
  | oRemove n f o hf hl hchild => simpa [Step.psi] using h
  | lBegin n f v hf hl ht => simpa [Step.psi] using h
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      exact State.writeTable_preserves_approx h hdom'
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      exact State.writeTable_preserves_approx h hdom'
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using h
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using h
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      exact State.writeTable_preserves_approx h hdom'
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using h
  | lUnload n f κ v o hf hl hg =>
      constructor
      · simp [Step.psi, h.ambient]
      · intro m
        simp [Step.psi]
        exact h.tables m

/-- **Equation (52) up to `≈`.**  For every rule except `O-Remove`, the
`edit` half writes only control fields: `next st ≈ Ψ st`.  `O-Remove` is
excluded because deleting a fiber can delete its raw table; in the paper
that case is handled by the vestigial-entry lemmas of Lemma 57. -/
theorem Step.edit_approx_psi_of_ne_remove {s : State N K E V} (st : Step s)
    (hno : st.kind ≠ StepKind.oRemove) :
    State.Approx (Step.next st) (Step.psi st s) := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      constructor
      · simp [Step.next, Step.edit, Step.psi]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hn]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, lookup_set_ne, hmn]
  | oRetire n f hf =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | oRemove n f o hf hl hchild =>
      simp [Step.kind] at hno
  | lBegin n f v hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lIter n f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, set_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn, set_set_eq]
  | lFinish n f ι κ v δ hinv hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, set_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn, set_set_eq]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertLand n f ι κ v δ hinv c hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, set_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn, set_set_eq]
  | lLeave n f κ v hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lUnload n f κ v o hf hl hg =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]

/-! ## Type-level traces and a first recovery-exactness result -/

/-- A predicate holds of every step in a type-level trace. -/
def Step.StepTrace.AllSteps {s t : State N K E V}
    (P : ∀ {s : State N K E V}, Step s → Prop) :
    Step.StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht => P st ∧ AllSteps P ht

/-- **A first recovery-exactness theorem.**  If a trace contains only
control-only steps, then the final state is `≈` to the initial state.
This is the base case of Theorem 61 in which no other fiber performs an
effect-carrying `Ψ`. -/
theorem StepTrace.recovery_exactness_control_trace {s t : State N K E V}
    (ht : Step.StepTrace s t)
    (hno : Step.StepTrace.AllSteps (fun {s} (st : Step s) => ControlOnly st) ht) :
    State.Approx t s := by
  cases ht with
  | nil s => exact State.Approx.refl s
  | cons st hnext ht =>
      rcases hno with ⟨hst, htail⟩
      have hstep : State.Approx (Step.next st) s := Step.edit_control_preserves_approx st hst
      have h := StepTrace.recovery_exactness_control_trace ht htail
      have htail_approx : State.Approx t (Step.next st) := (Eq.symm hnext) ▸ h
      exact State.Approx.trans htail_approx hstep

/-! ## Type-level trace folding: `t ≈ fold Ψ` -/

/-- Fold the `Ψ` maps of a type-level trace over a state.  This is the
right-hand side of Equation (52) when read along a whole trace. -/
def Step.StepTrace.foldPsi {s t : State N K E V} :
    Step.StepTrace s t → State N K E V → State N K E V
  | .nil _, x => x
  | .cons st _ ht, x => foldPsi ht (Step.psi st x)

/-- For two states that are being folded through the same trace, this
records that every step's acting name has the same presence in both
current states; it is exactly the side condition needed by
`Step.psi_preserves_approx` at each step. -/
def Step.StepTrace.PsiDomainAgrees {s t : State N K E V} (x y : State N K E V) :
    Step.StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      ((lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome) ∧
        PsiDomainAgrees (Step.psi st x) (Step.psi st y) ht

/-- Folding a trace through `≈`-equal states preserves `≈`, provided every
step's acting name is present in both states (or absent from both). -/
theorem StepTrace.foldPsi_preserves_approx {s t : State N K E V}
    (ht : Step.StepTrace s t) {x y : State N K E V}
    (h : State.Approx x y)
    (hdom : Step.StepTrace.PsiDomainAgrees x y ht) :
    State.Approx (Step.StepTrace.foldPsi ht x) (Step.StepTrace.foldPsi ht y) := by
  cases ht with
  | nil s => simpa [Step.StepTrace.foldPsi] using h
  | cons st hnext ht =>
      rcases hdom with ⟨hd, htail⟩
      have hpsi : State.Approx (Step.psi st x) (Step.psi st y) := Step.psi_preserves_approx st h hd
      have hrec := StepTrace.foldPsi_preserves_approx ht hpsi htail
      simpa [Step.StepTrace.foldPsi] using hrec

/-- Along a trace, every first step's `next` and `Ψ` state must keep the
same domain for all later steps.  This packages the side condition for the
trace-level Equation (52). -/
def Step.StepTrace.NextPsiDomainAgrees {s t : State N K E V} :
    Step.StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      Step.StepTrace.PsiDomainAgrees (Step.next st) (Step.psi st s) ht ∧
        NextPsiDomainAgrees ht

/-- **Trace-level Equation (52) up to `≈`.**  If no step is `O-Remove` and
the domain side condition holds, the final state is `≈` to the result of
folding every step's `Ψ` from the initial state. -/
theorem StepTrace.next_approx_foldPsi {s t : State N K E V}
    (ht : Step.StepTrace s t)
    (hno : Step.StepTrace.AllSteps (fun {s} (st : Step s) => st.kind ≠ StepKind.oRemove) ht)
    (hdom : Step.StepTrace.NextPsiDomainAgrees ht) :
    State.Approx t (Step.StepTrace.foldPsi ht s) := by
  cases ht with
  | nil s => exact State.Approx.refl s
  | cons st hnext ht =>
      rcases hno with ⟨hst, htail⟩
      rcases hdom with ⟨hd, htaildom⟩
      have hstep : State.Approx (Step.next st) (Step.psi st s) :=
        Step.edit_approx_psi_of_ne_remove st hst
      have htail_approx : State.Approx t (Step.StepTrace.foldPsi ht (Step.next st)) := by
        have h := StepTrace.next_approx_foldPsi ht htail htaildom
        simpa [hnext] using h
      have hfold : State.Approx (Step.StepTrace.foldPsi ht (Step.next st))
          (Step.StepTrace.foldPsi ht (Step.psi st s)) :=
        StepTrace.foldPsi_preserves_approx ht hstep hd
      have hgoal : State.Approx t (Step.StepTrace.foldPsi ht (Step.psi st s)) :=
        State.Approx.trans htail_approx hfold
      simpa [Step.StepTrace.foldPsi] using hgoal

/-- If no step of a trace acts on `n`, the fiber at `n` is unchanged. -/
theorem StepTrace.lookup_eq_of_never {s t : State N K E V}
    (ht : Step.StepTrace s t) {n : N} {f : Fiber N K V E}
    (hstart : lookup s.reg n = some f)
    (hno : Step.StepTrace.AllSteps (fun {s} (st : Step s) => st.name ≠ n) ht) :
    lookup t.reg n = some f := by
  cases ht with
  | nil s => exact hstart
  | cons st hnext ht =>
      rcases hno with ⟨hst, htail⟩
      have hnext_lookup : lookup (Step.next st).reg n = some f := by
        rw [Step.lookup_next_eq_of_ne st (fun h => hst h.symm)]
        exact hstart
      have htail' : lookup t.reg n = some f := by
        refine StepTrace.lookup_eq_of_never ht ?_ htail
        simpa [hnext] using hnext_lookup
      exact htail'

/-- **Recovery exactness for an episode with no `n` steps.**  If the fiber
`n` was just begun (accumulator `id`) and never steps again, applying its
accumulator at the end recovers the state produced by folding the other
steps' `Ψ` maps from the beginning. -/
theorem StepTrace.recovery_exactness_no_steps_of {s t : State N K E V}
    (ht : Step.StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc = .loading f.comp.iter id v)
    (hno_n : Step.StepTrace.AllSteps (fun {s} (st : Step s) => st.name ≠ n) ht)
    (hno_remove : Step.StepTrace.AllSteps (fun {s} (st : Step s) => st.kind ≠ StepKind.oRemove) ht)
    (hdom : Step.StepTrace.NextPsiDomainAgrees ht) :
    State.Approx (State.applyAcc t n) (Step.StepTrace.foldPsi ht s) := by
  rcases hstart with ⟨f, hf, hl⟩
  have ht_lookup : lookup t.reg n = some f := StepTrace.lookup_eq_of_never ht hf hno_n
  have hacc_eq : State.applyAcc t n = t := State.applyAcc_of_loading_id ht_lookup hl
  rw [hacc_eq]
  exact StepTrace.next_approx_foldPsi ht hno_remove hdom

/-! ## Resolution coherence (Theorem 64, iteration part) -/

/-- A type-level trace predicate: the committed view of `n` is `v` at the
source of every step in the trace and at that step's next state. -/
def Step.StepTrace.ViewFixedAlong {s t : State N K E V} (n : N) (v : K → Option N) :
    Step.StepTrace s t → Prop
  | .nil _ => True
  | .cons st _ ht =>
      (st.name ≠ n ∨
        (∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v ∧
              ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v)) ∧
      ViewFixedAlong n v ht

/-- **Theorem 64, loading-step dichotomy.**  A lifecycle step acting on a
`loading` fiber is one of the five loading rules: `L-Iter`, `L-Finish`,
`L-Raise`, `L-Divert` (abort or landing).  The first two keep the initial
loading interval; the last three leave it. -/
theorem Step.kind_of_loading_lifecycle {s : State N K E V} (st : Step s)
    {n : N} {f : Fiber N K V E} {ι : Iterator (CoefCtx K V) E}
    {κ : CoefCtx K V → CoefCtx K V} {v : K → Option N}
    (hn : st.name = n)
    (hlife : StepKind.isLifecycle st.kind)
    (hf : lookup s.reg n = some f)
    (hl : f.lc = .loading ι κ v) :
    st.kind = StepKind.lIter ∨ st.kind = StepKind.lFinish ∨
    st.kind = StepKind.lRaise ∨ st.kind = StepKind.lDivertAbort ∨
    st.kind = StepKind.lDivertLand := by
  cases st with
  | lIter n0 f0 ι0 κ0 v0 ι' δ hinv hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inl rfl
  | lFinish n0 f0 ι0 κ0 v0 δ hinv hreach hf0 hl0 ht hstep =>
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
  | lDivertLand n0 f0 ι0 κ0 v0 δ hinv c hreach hf0 hl0 ht hstep =>
      simp [Step.name] at hn
      subst n0
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | oInsert n0 c p hn0 hp hdisj =>
      simp [Step.name, Step.kind, StepKind.isLifecycle] at hn hlife
  | oRetire n0 f0 hf0 =>
      simp [Step.name, Step.kind, StepKind.isLifecycle] at hn hlife
  | oRemove n0 f0 o hf0 hl0 hchild =>
      simp [Step.name, Step.kind, StepKind.isLifecycle] at hn hlife
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

/-- An `L-Iter` or `L-Finish` step acting on a fiber whose committed view
is `v` preserves that committed view. -/
theorem Step.view_preserved_of_iter {s : State N K E V} (st : Step s)
    {n : N} {v : K → Option N}
    (hn : st.name = n)
    (hk : st.kind = StepKind.lIter ∨ st.kind = StepKind.lFinish)
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v) :
    ∃ f', lookup (Step.next st).reg n = some f' ∧ f'.lc.viewOf = v := by
  cases st with
  | lIter n0 f ι κ v0 ι' δ hinv hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hstart with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      refine ⟨{ f with table := δ, lc := .loading ι' (κ ∘ hinv) v0 }, ?_, ?_⟩
      · simp [Step.next, Step.edit, Step.psi, hf, set_set_eq]
      · simp [Lifecycle.viewOf, hv0]
  | lFinish n0 f ι κ v0 δ hinv hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hstart with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      refine ⟨{ f with table := δ, lc := .active (κ ∘ hinv) v0 }, ?_, ?_⟩
      · simp [Step.next, Step.edit, Step.psi, hf, set_set_eq]
      · simp [Lifecycle.viewOf, hv0]
  | _ =>
      simp [Step.name, Step.kind] at hn hk

/-- An `L-Iter` or `L-Finish` step acting on a fiber whose committed view
is `v` runs against exactly that resolution `v`. -/
theorem Step.target_eq_of_iter_view {s : State N K E V} (st : Step s)
    {n : N} {v : K → Option N}
    (hn : st.name = n)
    (hk : st.kind = StepKind.lIter ∨ st.kind = StepKind.lFinish)
    (hview : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v) :
    Full.targetOf s.reg n = some v := by
  cases st with
  | lIter n0 f ι κ v0 ι' δ hinv hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hview with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      simpa [hv0] using ht
  | lFinish n0 f ι κ v0 δ hinv hreach hf hl ht hstep =>
      simp [Step.name] at hn
      subst n0
      rcases hview with ⟨f₀, hf₀, hv₀⟩
      have hf_eq : f = f₀ := Option.some.inj (hf.symm.trans hf₀)
      subst f₀
      have hv0 : v0 = v := by
        rw [hl] at hv₀
        exact hv₀
      simpa [hv0] using ht
  | _ =>
      simp [Step.name, Step.kind] at hn hk

/-- **Theorem 64, view-fixity half.**  In a trace whose `n`-steps are only
`L-Iter`/`L-Finish`, the committed view of `n` is fixed to `v` throughout. -/
theorem StepTrace.view_fixed_of_iteration_trace {s t : State N K E V}
    (ht : Step.StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v)
    (hall : Step.StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ st.kind = StepKind.lIter ∨ st.kind = StepKind.lFinish) ht) :
    Step.StepTrace.ViewFixedAlong n v ht := by
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
              rw [Step.lookup_next_eq_of_ne st hne']
              exact hf
            exact ⟨f, hf', hv⟩
        exact ih (by rwa [hnext] at hstart') htail

/-- **Theorem 64, Eq. (59).**  In the initial interval of an episode, every
`L-Iter`/`L-Finish` of the transition runs against the one committed
resolution `v`. -/
theorem StepTrace.resolution_coherent_of_iteration_trace {s t : State N K E V}
    (ht : Step.StepTrace s t) {n : N} {v : K → Option N}
    (hstart : ∃ f, lookup s.reg n = some f ∧ f.lc.viewOf = v)
    (hall : Step.StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ st.kind = StepKind.lIter ∨ st.kind = StepKind.lFinish) ht) :
    Step.StepTrace.AllSteps (fun {s} (st : Step s) =>
        st.name ≠ n ∨ Full.targetOf s.reg n = some v) ht := by
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
              rw [Step.lookup_next_eq_of_ne st hne']
              exact hf
            exact ⟨f, hf', hv⟩
        exact ih (by rwa [hnext] at hstart') htail

end Full

end Cordix
