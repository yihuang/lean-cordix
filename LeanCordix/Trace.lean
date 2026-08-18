import LeanCordix.Recovery

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Faithful trace-level recovery -/

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

end Cordix
