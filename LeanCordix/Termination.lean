import LeanCordix.Trace

/-!
# LeanCordix.Termination — Theorem 66.2 termination scaffolding

This module ports the termination quantities and combinatorial bounds from
the deleted legacy `Termination.lean` onto the current faithful
`StepTrace`/`State` model.

* `StepTrace.length` — number of steps in a trace;
* `StepTrace.countFor` — number of steps acting on a given fiber;
* `StepTrace.targetTurns` — number of times a fiber's target view changes
  along a trace (Eq. 61);
* `StepTrace.countFor_le_mul_of_interval_bound` — the combinatorial half of
  Theorem 66.2: if every source-constant target interval has at most `B`
  steps acting on `n`, then
  `countFor ht n ≤ B * (targetTurns ht n + 1)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

noncomputable section
open Classical

namespace StepTrace

/-- The number of steps in a type-level trace. -/
def length {s t : State N K E V} (ht : StepTrace s t) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons _ _ ht => 1 + length ht

/-- The number of steps in a trace that act on a particular name. -/
def countFor {s t : State N K E V} (ht : StepTrace s t) (n : N) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons st _ ht =>
      (if st.name = n then 1 else 0) + countFor ht n

/-- The number of times a fiber's target view changes along a trace,
Eq. (61). -/
def targetTurns {s t : State N K E V} (ht : StepTrace s t) (n : N) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons st _ ht =>
      (if State.targetOf s n ≠ State.targetOf (Step.next st) n then 1 else 0) +
        targetTurns ht n

@[simp] theorem length_nil (s : State N K E V) :
    length (StepTrace.nil s) = 0 := rfl

@[simp] theorem length_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : StepTrace s₂ s₃) :
    length (StepTrace.cons st hnext ht) = 1 + length ht := rfl

@[simp] theorem countFor_nil (s : State N K E V) (n : N) :
    countFor (StepTrace.nil s) n = 0 := rfl

@[simp] theorem countFor_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : StepTrace s₂ s₃) (n : N) :
    countFor (StepTrace.cons st hnext ht) n =
      (if st.name = n then 1 else 0) + countFor ht n := rfl

@[simp] theorem targetTurns_nil (s : State N K E V) (n : N) :
    targetTurns (StepTrace.nil s) n = 0 := rfl

/-- Every step counted by `countFor` acts on `n`; if no step acts on `n`,
the count is zero. -/
theorem countFor_eq_zero_of_no_steps {s t : State N K E V}
    (ht : StepTrace s t) {n : N}
    (hno : StepTrace.AllSteps (fun {s} (st : Step s) => st.name ≠ n) ht) :
    countFor ht n = 0 := by
  cases ht with
  | nil s => rfl
  | cons st hnext ht =>
      rcases hno with ⟨hst, htail⟩
      have htail' : countFor ht n = 0 := countFor_eq_zero_of_no_steps ht htail
      simp [countFor, hst, htail']

/-- The per-fiber count cannot exceed the trace length. -/
theorem countFor_le_length {s t : State N K E V} (ht : StepTrace s t) (n : N) :
    countFor ht n ≤ length ht := by
  induction ht with
  | nil s => simp [countFor, length]
  | cons st hnext ht ih =>
      by_cases hname : st.name = n
      · simp [countFor, length, hname, ih]
      · simp [countFor, length, hname, ih]
        omega

@[simp] theorem targetTurns_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : StepTrace s₂ s₃) (n : N) :
    targetTurns (StepTrace.cons st hnext ht) n =
      (if State.targetOf s₁ n ≠ State.targetOf (Step.next st) n then 1 else 0) +
        targetTurns ht n := by
  simp [targetTurns, hnext]

/-- The number of target turns cannot exceed the trace length. -/
theorem targetTurns_le_length {s t : State N K E V}
    (ht : StepTrace s t) (n : N) :
    targetTurns ht n ≤ length ht := by
  induction ht with
  | nil s => simp [targetTurns, length]
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      simp [targetTurns, length, ih]
      by_cases h : State.targetOf s₁ n = State.targetOf (Step.next st) n
      · simp [h]
        omega
      · simp [h]
        omega

/-! ## Interval splitting and the global counting bound -/

/-- Concatenate two type-level traces. -/
def append {s m t : State N K E V} : StepTrace s m → StepTrace m t → StepTrace s t
  | .nil _, h2 => h2
  | .cons st hnext h1, h2 => .cons st hnext (append h1 h2)

/-- Whether a trace is the empty trace. -/
def IsNil {s t : State N K E V} : StepTrace s t → Prop
  | .nil _ => True
  | .cons _ _ _ => False

@[simp] theorem length_append {s m t : State N K E V} (h1 : StepTrace s m) (h2 : StepTrace m t) :
    length (append h1 h2) = length h1 + length h2 := by
  induction h1 with
  | nil s => simp [append, length]
  | cons st hnext h1 ih => simp [append, length, ih, Nat.add_assoc]

@[simp] theorem countFor_append {s m t : State N K E V} (h1 : StepTrace s m) (h2 : StepTrace m t) (n : N) :
    countFor (append h1 h2) n = countFor h1 n + countFor h2 n := by
  induction h1 with
  | nil s => simp [append, countFor]
  | cons st hnext h1 ih => simp [append, countFor, ih, Nat.add_assoc]

@[simp] theorem targetTurns_append {s m t : State N K E V} (h1 : StepTrace s m) (h2 : StepTrace m t) (n : N) :
    targetTurns (append h1 h2) n = targetTurns h1 n + targetTurns h2 n := by
  induction h1 with
  | nil s => simp [append, targetTurns]
  | cons st hnext h1 ih =>
      simp [append, targetTurns, targetTurns_cons, ih, Nat.add_assoc]

/-- A trace all of whose source states have the same target view `v` for the
fiber `n`.  This is the paper's “maximal interval on which `target_n` is
constant”, except that we do not require maximality; the bound below only
needs the constancy property. -/
def SourceTargetConst {s t : State N K E V} (ht : StepTrace s t) (n : N) (v : Option (K → Option N)) : Prop :=
  match ht with
  | .nil _ => True
  | .cons st _ ht => State.targetOf s n = v ∧ SourceTargetConst ht n v

/-- The result of splitting a trace at the first place where the source
target of `n` changes.  The fields carry the decomposition
`ht = append pre post`, the constancy of the prefix, the fact that the
suffix is shorter, and the turn-count equations needed for the recursive
bound. -/
structure Split {s t : State N K E V} (ht : StepTrace s t) (n : N) where
  mid : State N K E V
  pre : StepTrace s mid
  post : StepTrace mid t
  eq : ht = append pre post
  source_const : SourceTargetConst pre n (State.targetOf s n)
  post_len_le : length post ≤ length ht
  post_len_lt : (¬ IsNil post) → length post < length ht
  turns_eq : targetTurns ht n = targetTurns pre n + targetTurns post n
  pre_turns_le_one : targetTurns pre n ≤ 1
  pre_turns_eq_one_of_post : (¬ IsNil post) → targetTurns pre n = 1

/-- Split a trace at the first change of `State.targetOf _ n`. -/
def splitFirstInterval {s t : State N K E V} (ht : StepTrace s t) (n : N) : Split ht n := by
  induction ht with
  | nil s =>
      exact ⟨s, .nil s, .nil s, rfl, by simp [SourceTargetConst],
        by simp [length],
        by intro h; exact False.elim (h trivial),
        by simp [targetTurns], by simp [targetTurns],
        by intro h; exact False.elim (h trivial)⟩
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      subst hnext
      by_cases h : State.targetOf (Step.next st) n = State.targetOf s₁ n
      · exact ⟨ih.mid, .cons st rfl ih.pre, ih.post, by
            simp [append, ih.eq], by
            simp [SourceTargetConst, h.symm, ih.source_const],
          by
            simp [length]
            simpa [Nat.add_comm] using Nat.le_succ_of_le ih.post_len_le,
          by
            intro hpost
            simpa [Nat.add_comm] using Nat.lt_succ_of_le ih.post_len_le,
          by
            simp [targetTurns_cons, h, ih.turns_eq, Nat.add_assoc],
          by
            simp [targetTurns_cons, h, ih.pre_turns_le_one],
          by
            intro hpost
            have h' : ¬ IsNil ih.post := by
              intro hnil
              exact hpost hnil
            simp [targetTurns_cons, h, ih.pre_turns_eq_one_of_post h']⟩
      · exact ⟨Step.next st, .cons st rfl (.nil _), ht, rfl, by
            simp [SourceTargetConst],
          by simp [length],
          by
            intro _
            simp [Nat.add_comm],
          by
            simp [targetTurns_cons, h, targetTurns],
          by
            simp [targetTurns_cons]
            by_cases h2 : State.targetOf s₁ n = State.targetOf (Step.next st) n
            · simp [h2]
            · simp [h2],
          by
            intro _
            simp [targetTurns_cons]
            exact fun hEq => h hEq.symm⟩

/-- **Theorem 66.2, combinatorial half.**  If every interval on which
`State.targetOf _ n` is source-constant has at most `B` steps acting on `n`,
then `countFor ht n ≤ B * (targetTurns ht n + 1)`. -/
theorem countFor_le_mul_of_interval_bound (B : Nat) (n : N)
    (hB : ∀ {s t : State N K E V} (ht : StepTrace s t) {v : Option (K → Option N)},
      SourceTargetConst ht n v → countFor ht n ≤ B) :
    ∀ {s t : State N K E V} (ht : StepTrace s t),
      countFor ht n ≤ B * (targetTurns ht n + 1) := by
  intro s t ht
  let sp := splitFirstInterval ht n
  rcases sp with ⟨mid, pre, post, eq, source_const, post_len_le, post_len_lt, turns_eq, pre_turns_le_one, pre_turns_eq_one_of_post⟩
  have hBpre : countFor pre n ≤ B :=
    hB pre (v := State.targetOf s n) source_const
  have hcount : countFor ht n = countFor pre n + countFor post n := by
    have h := congrArg (fun h : StepTrace s t => countFor h n) eq
    simpa [countFor_append] using h
  cases post with
  | nil mid' =>
      have hturns : targetTurns ht n = targetTurns pre n := by
        rw [turns_eq]
        simp [targetTurns]
      have hpos : 0 < targetTurns pre n + 1 := by omega
      have hmul : B ≤ B * (targetTurns pre n + 1) := Nat.le_mul_of_pos_right B hpos
      have hle : countFor pre n ≤ B * (targetTurns pre n + 1) := Nat.le_trans hBpre hmul
      simpa [hcount, hturns] using hle
  | @cons mid' mid'' t' st' hnext' post' =>
      let postAll : StepTrace mid t := StepTrace.cons st' hnext' post'
      have hrec := countFor_le_mul_of_interval_bound B n hB postAll
      have hpre_turns : targetTurns pre n = 1 := pre_turns_eq_one_of_post (by simp [IsNil])
      have hturns : targetTurns ht n = 1 + targetTurns postAll n := by
        rw [turns_eq, hpre_turns]
      have hcalc : countFor postAll n ≤ B * (targetTurns postAll n + 1) := hrec
      have hsum : countFor pre n + countFor postAll n ≤ B * (targetTurns postAll n + 2) := by
        have h1 := Nat.add_le_add hBpre hcalc
        have hEq : B + B * (targetTurns postAll n + 1) = B * (targetTurns postAll n + 2) := by
          rw [show targetTurns postAll n + 2 = (targetTurns postAll n + 1) + 1 by omega]
          simp [Nat.mul_add, Nat.mul_one]
          omega
        simpa [hEq] using h1
      rw [hcount, hturns]
      have hEq2 : 1 + targetTurns postAll n + 1 = targetTurns postAll n + 2 := by omega
      rw [hEq2]
      exact hsum
termination_by s t ht => length ht
decreasing_by
  simp_wf
  exact post_len_lt (by simp [IsNil])

/-- **Theorem 66.2, packaged for the paper's `len` assumption.**
If the per-interval bound is instantiated with `B = len n + 4`, the global
bound reads `countFor ht n ≤ (len n + 4) * (targetTurns ht n + 1)`. -/
theorem countFor_le_targetTurns_of_len (len : N → Nat)
    (hinterval : ∀ {s t : State N K E V} (ht : StepTrace s t) {n : N} {v : Option (K → Option N)},
      SourceTargetConst ht n v → countFor ht n ≤ len n + 4) :
    ∀ {s t : State N K E V} (ht : StepTrace s t) (n : N),
      countFor ht n ≤ (len n + 4) * (targetTurns ht n + 1) := by
  intro s t ht n
  let hB' : ∀ {s' t' : State N K E V} (ht' : StepTrace s' t') {v : Option (K → Option N)},
      SourceTargetConst ht' n v → countFor ht' n ≤ len n + 4 := by
    intro s' t' ht' v hc
    exact hinterval (n := n) (v := v) ht' hc
  exact countFor_le_mul_of_interval_bound (len n + 4) n hB' ht

/-! ## Decomposition into loading and non-loading lifecycle steps

The per-interval bound still requires the paper's `len` hypothesis.  The
following counting split separates loading-phase steps (`L-Iter`,
`L-Finish`, `L-Raise`, `L-Divert`) from boundary steps (`L-Begin`,
`L-Leave`, `L-Unload`). -/

/-- A loading-phase lifecycle kind: a step that can occur while the fiber
is in `loading`. -/
def IsLoadingKind (k : Full.StepKind) : Prop :=
  k = Full.StepKind.lIter ∨ k = Full.StepKind.lFinish ∨ k = Full.StepKind.lRaise ∨
    k = Full.StepKind.lDivertAbort ∨ k = Full.StepKind.lDivertLand

/-- A non-loading lifecycle kind: a step that opens, leaves, or closes an
activation episode. -/
def IsNonLoadingKind (k : Full.StepKind) : Prop :=
  k = Full.StepKind.lBegin ∨ k = Full.StepKind.lLeave ∨ k = Full.StepKind.lUnload

/-- The number of loading-phase steps acting on `n`. -/
def loadingCount {s t : State N K E V} (ht : StepTrace s t) (n : N) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons st _ ht =>
      (if st.name = n ∧ IsLoadingKind st.kind then 1 else 0) + loadingCount ht n

/-- The number of non-loading lifecycle steps acting on `n`. -/
def nonLoadingCount {s t : State N K E V} (ht : StepTrace s t) (n : N) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons st _ ht =>
      (if st.name = n ∧ IsNonLoadingKind st.kind then 1 else 0) + nonLoadingCount ht n

/-- For a lifecycle-only trace, `countFor` splits into the loading-phase
count and the boundary-step count. -/
theorem countFor_eq_loading_add_nonLoading {s t : State N K E V}
    (ht : StepTrace s t) (n : N)
    (hlife : StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht) :
    countFor ht n = loadingCount ht n + nonLoadingCount ht n := by
  induction ht with
  | nil s => simp [countFor, loadingCount, nonLoadingCount]
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      rcases hlife with ⟨hlife_st, hlife_tail⟩
      have ih' := ih hlife_tail
      by_cases hname : st.name = n
      · simp [countFor, loadingCount, nonLoadingCount, hname]
        cases st <;> simp [IsLoadingKind, IsNonLoadingKind, Step.kind, Full.StepKind.isLifecycle]
          at hlife_st ⊢ <;> omega
      · simp [countFor, loadingCount, nonLoadingCount, hname, ih']

/-! ## A lifecycle-aware interval bound

The original `countFor_le_mul_of_interval_bound` assumes the per-interval
bound is available for every source-constant trace.  The paper's `len`
hypothesis is stated for lifecycle-only intervals, so we need the same
combinatorial recursion with a lifecycle-only hypothesis threaded through
it. -/

/-- If a concatenated trace satisfies a step predicate, its left part does. -/
theorem AllSteps_of_append_left {s m t : State N K E V}
    (P : ∀ {s : State N K E V}, Step s → Prop)
    (h1 : StepTrace s m) (h2 : StepTrace m t) :
    StepTrace.AllSteps P (append h1 h2) → StepTrace.AllSteps P h1 := by
  induction h1 with
  | nil s => intro h; trivial
  | cons st hnext h1 ih =>
      intro h
      rcases h with ⟨hp, htail⟩
      exact ⟨hp, ih h2 htail⟩

/-- If a concatenated trace satisfies a step predicate, its right part does. -/
theorem AllSteps_of_append_right {s m t : State N K E V}
    (P : ∀ {s : State N K E V}, Step s → Prop)
    (h1 : StepTrace s m) (h2 : StepTrace m t) :
    StepTrace.AllSteps P (append h1 h2) → StepTrace.AllSteps P h2 := by
  induction h1 with
  | nil s => intro h; simpa [append] using h
  | cons st hnext h1 ih =>
      intro h
      rcases h with ⟨_, htail⟩
      exact ih h2 htail

/-- **Theorem 66.2, combinatorial half, lifecycle-only variant.**
Same as `countFor_le_mul_of_interval_bound`, but the per-interval hypothesis
is only required for lifecycle-only source-constant intervals. -/
theorem countFor_le_mul_of_interval_bound_of_lifecycle (B : Nat) (n : N)
    (hB : ∀ {s t : State N K E V} (ht : StepTrace s t) {v : Option (K → Option N)},
      SourceTargetConst ht n v →
      StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht →
      countFor ht n ≤ B) :
    ∀ {s t : State N K E V} (ht : StepTrace s t),
      StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht →
      countFor ht n ≤ B * (targetTurns ht n + 1) := by
  intro s t ht hlife
  let sp := splitFirstInterval ht n
  rcases sp with ⟨mid, pre, post, eq, source_const, post_len_le, post_len_lt, turns_eq, pre_turns_le_one, pre_turns_eq_one_of_post⟩
  have hlife_append : StepTrace.AllSteps
      (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) (append pre post) := by
    simpa [eq] using hlife
  have hlife_pre : StepTrace.AllSteps
      (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) pre :=
    AllSteps_of_append_left
      (P := fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) pre post hlife_append
  have hlife_post : StepTrace.AllSteps
      (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) post :=
    AllSteps_of_append_right
      (P := fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) pre post hlife_append
  have hBpre : countFor pre n ≤ B :=
    hB pre (v := State.targetOf s n) source_const hlife_pre
  have hcount : countFor ht n = countFor pre n + countFor post n := by
    have h := congrArg (fun h : StepTrace s t => countFor h n) eq
    simpa [countFor_append] using h
  cases post with
  | nil mid' =>
      have hturns : targetTurns ht n = targetTurns pre n := by
        rw [turns_eq]
        simp [targetTurns]
      have hpos : 0 < targetTurns pre n + 1 := by omega
      have hmul : B ≤ B * (targetTurns pre n + 1) := Nat.le_mul_of_pos_right B hpos
      have hle : countFor pre n ≤ B * (targetTurns pre n + 1) := Nat.le_trans hBpre hmul
      simpa [hcount, hturns] using hle
  | @cons mid' mid'' t' st' hnext' post' =>
      let postAll : StepTrace mid t := StepTrace.cons st' hnext' post'
      have hpost_hlife : StepTrace.AllSteps
          (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) postAll := by
        rcases hlife_post with ⟨hst', hpost_tail⟩
        exact ⟨hst', hpost_tail⟩
      have hrec := countFor_le_mul_of_interval_bound_of_lifecycle B n hB postAll hpost_hlife
      have hpre_turns : targetTurns pre n = 1 := pre_turns_eq_one_of_post (by simp [IsNil])
      have hturns : targetTurns ht n = 1 + targetTurns postAll n := by
        rw [turns_eq, hpre_turns]
      have hcalc : countFor postAll n ≤ B * (targetTurns postAll n + 1) := hrec
      have hsum : countFor pre n + countFor postAll n ≤ B * (targetTurns postAll n + 2) := by
        have h1 := Nat.add_le_add hBpre hcalc
        have hEq : B + B * (targetTurns postAll n + 1) = B * (targetTurns postAll n + 2) := by
          rw [show targetTurns postAll n + 2 = (targetTurns postAll n + 1) + 1 by omega]
          simp [Nat.mul_add, Nat.mul_one]
          omega
        simpa [hEq] using h1
      rw [hcount, hturns]
      have hEq2 : 1 + targetTurns postAll n + 1 = targetTurns postAll n + 2 := by omega
      rw [hEq2]
      exact hsum
termination_by s t ht => length ht
decreasing_by
  simp_wf
  exact post_len_lt (by simp [IsNil])

/-! ## Boundary-step budget inside a source-constant interval

The four non-loading lifecycle steps are `L-Begin`, `L-Leave`, and
`L-Unload`.  The budget below tracks the strongest possible remaining
bound from each lifecycle state; the per-step inequalities are verified by
case analysis on the faithful `Step` constructors. -/

/-- A conservative upper bound on the number of future non-loading steps
from a lifecycle state while `targetOf n` is held constant. -/
def NonLoadingBudget (v : Option (K → Option N)) (lc : Lifecycle N K V E) : Nat :=
  match lc with
  | .inactive none => 2
  | .inactive (some _) => 0
  | .loading _ _ w => if v = some w then 1 else 3
  | .active _ w => if v = some w then 0 else 4
  | .unloading _ w none => 3
  | .unloading _ w (some _) => 1

/-- The same budget read off a state's registry. -/
def nonLoadingBudgetState (s : State N K E V) (n : N) (v : Option (K → Option N)) : Nat :=
  match lookup s.reg n with
  | some f => NonLoadingBudget v f.lc
  | none => 0

/-- A source-constant lifecycle-only trace never spends more non-loading
steps than the budget of its initial state. -/
theorem nonLoadingCount_le_budget {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : Option (K → Option N)}
    (hconst : SourceTargetConst ht n v)
    (hlife : StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht) :
    nonLoadingCount ht n ≤ nonLoadingBudgetState s n v := by
  induction ht with
  | nil s => simp [nonLoadingCount, nonLoadingBudgetState]
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      rcases hconst with ⟨htarget, htail_const⟩
      rcases hlife with ⟨hlife_st, htail_life⟩
      by_cases hst : st.name = n
      · subst hnext
        cases st with
        | oInsert n0 c p hn0 hp hdisj =>
            simp [Step.name] at hst
            subst n0
            simp [Step.kind, Full.StepKind.isLifecycle] at hlife_st
        | oRetire n0 f hf =>
            simp [Step.name] at hst
            subst n0
            simp [Step.kind, Full.StepKind.isLifecycle] at hlife_st
        | oRemove n0 f o hf hl hchild =>
            simp [Step.name] at hst
            subst n0
            simp [Step.kind, Full.StepKind.isLifecycle] at hlife_st
        | lBegin n0 f v0 hf hl ht0 htable =>
            simp [Step.name] at hst
            subst n0
            have hv0 : v = some v0 := by
              change State.targetOf s₁ n = some v0 at ht0
              rw [← htarget]
              exact ht0
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 1 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, lookup_set_eq, hv0] using htail
            simp [nonLoadingCount, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, lookup_set_eq, hv0]
            change 1 + ht.nonLoadingCount n ≤ 2
            omega
        | lIter n0 f ι κ v0 ι' δ h hreach hf hl ht0 hstep =>
            simp [Step.name] at hst
            subst n0
            have hv0 : v = some v0 := by
              change State.targetOf s₁ n = some v0 at ht0
              rw [← htarget]
              exact ht0
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 1 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hv0] using htail
            simp [nonLoadingCount, IsLoadingKind, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hv0]
            change ht.nonLoadingCount n ≤ 1
            omega
        | lFinish n0 f ι κ v0 δ h hreach hf hl ht0 hstep =>
            simp [Step.name] at hst
            subst n0
            have hv0 : v = some v0 := by
              change State.targetOf s₁ n = some v0 at ht0
              rw [← htarget]
              exact ht0
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 0 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hv0] using htail
            simp [nonLoadingCount, IsLoadingKind, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hv0]
            change ht.nonLoadingCount n ≤ 1
            omega
        | lRaise n0 f ι κ v0 e hreach hf hl hstep =>
            simp [Step.name] at hst
            subst n0
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 1 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, lookup_set_eq] using htail
            simp [nonLoadingCount, IsLoadingKind, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, lookup_set_eq]
            have hsrc_ge : 1 ≤ (if v = some v0 then 1 else 3) := by
              by_cases h : v = some v0 <;> simp [h]
            exact Nat.le_trans htail' hsrc_ge
        | lDivertAbort n0 f ι κ v0 hreach hf hl ht0 =>
            simp [Step.name] at hst
            subst n0
            have hvne : v ≠ some v0 := by
              intro heq
              change State.targetOf s₁ n ≠ some v0 at ht0
              rw [htarget] at ht0
              exact ht0 heq
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 3 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, lookup_set_eq, hvne] using htail
            simp [nonLoadingCount, IsLoadingKind, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, lookup_set_eq, hvne]
            change ht.nonLoadingCount n ≤ 3
            omega
        | lDivertLand n0 f ι κ v0 δ h c hreach hf hl ht0 hstep =>
            simp [Step.name] at hst
            subst n0
            have hvne : v ≠ some v0 := by
              intro heq
              change State.targetOf s₁ n ≠ some v0 at ht0
              rw [htarget] at ht0
              exact ht0 heq
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 3 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hvne] using htail
            simp [nonLoadingCount, IsLoadingKind, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, hstep, State.writeEffect_eq_of_lookup, lookup_set_eq, hvne]
            change ht.nonLoadingCount n ≤ 3
            omega
        | lLeave n0 f κ v0 hf hl ht0 =>
            simp [Step.name] at hst
            subst n0
            have hvne : v ≠ some v0 := by
              intro heq
              change State.targetOf s₁ n ≠ some v0 at ht0
              rw [htarget] at ht0
              exact ht0 heq
            have htail := ih htail_const htail_life
            have htail' : ht.nonLoadingCount n ≤ 3 := by
              simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                hf, hl, lookup_set_eq, hvne] using htail
            simp [nonLoadingCount, IsNonLoadingKind, Step.kind, Step.name,
              nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
              hf, hl, lookup_set_eq, hvne]
            change 1 + ht.nonLoadingCount n ≤ 4
            omega
        | lUnload n0 f κ v0 o hf hl hg =>
            simp [Step.name] at hst
            subst n0
            have htail := ih htail_const htail_life
            cases o with
            | none =>
                have htail' : ht.nonLoadingCount n ≤ 2 := by
                  simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                    hf, hl, State.writeEffect_eq_of_lookup, lookup_set_eq] using htail
                simp [nonLoadingCount, IsNonLoadingKind, Step.kind, Step.name,
                  nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                  hf, hl, State.writeEffect_eq_of_lookup, lookup_set_eq]
                change 1 + ht.nonLoadingCount n ≤ 3
                omega
            | some e =>
                have htail' : ht.nonLoadingCount n ≤ 0 := by
                  simpa [nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                    hf, hl, State.writeEffect_eq_of_lookup, lookup_set_eq] using htail
                simp [nonLoadingCount, IsNonLoadingKind, Step.kind, Step.name,
                  nonLoadingBudgetState, NonLoadingBudget, Step.next, Step.edit, Step.psi,
                  hf, hl, State.writeEffect_eq_of_lookup, lookup_set_eq]
                change 1 + ht.nonLoadingCount n ≤ 1
                omega
      · have htail_ih := ih htail_const htail_life
        have hnext_lookup : lookup s₂.reg n = lookup s₁.reg n := by
          rw [← hnext]
          rw [Step.factorization]
          rw [Step.edit_preserves_lookup_ne st (Ne.symm hst)]
          exact Step.psi_preserves_lookup_ne st (Ne.symm hst)
        have hbudget_eq : nonLoadingBudgetState s₁ n v = nonLoadingBudgetState s₂ n v := by
          unfold nonLoadingBudgetState
          rw [hnext_lookup]
        have hcount : nonLoadingCount (StepTrace.cons st hnext ht) n = nonLoadingCount ht n := by
          simp [nonLoadingCount, hst]
        rw [hcount, hbudget_eq]
        exact htail_ih

/-- **Theorem 66.2(A), boundary part.**  In a lifecycle-only trace whose
source target for `n` is constant, at most four non-loading lifecycle steps
can act on `n`. -/
theorem nonLoadingCount_le_four_of_source_const {s t : State N K E V}
    (ht : StepTrace s t) {n : N} {v : Option (K → Option N)}
    (hconst : SourceTargetConst ht n v)
    (hlife : StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht) :
    nonLoadingCount ht n ≤ 4 := by
  have hle := nonLoadingCount_le_budget ht hconst hlife
  have hbudget : nonLoadingBudgetState s n v ≤ 4 := by
    unfold nonLoadingBudgetState NonLoadingBudget
    cases h : lookup s.reg n with
    | none => simp
    | some f =>
        cases hlc : f.lc with
        | inactive o =>
            cases o with
            | none => simp [hlc]
            | some _ => simp [hlc]
        | loading _ _ w => by_cases h : v = some w <;> simp [hlc, h]
        | active _ w => by_cases h : v = some w <;> simp [hlc, h]
        | unloading _ _ o =>
            cases o with
            | none => simp [hlc]
            | some _ => simp [hlc]
  exact Nat.le_trans hle hbudget

/-- **Theorem 66.2(A), packaged with `len`.**  On a source-constant
lifecycle-only interval, the loading steps are bounded by `len n` and the
four boundary steps by the constant `4`. -/
theorem countFor_le_len_add_four_of_source_const (len : N → Nat)
    {s t : State N K E V} (ht : StepTrace s t) {n : N} {v : Option (K → Option N)}
    (hconst : SourceTargetConst ht n v)
    (hlife : StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht)
    (hloading : loadingCount ht n ≤ len n) :
    countFor ht n ≤ len n + 4 := by
  rw [countFor_eq_loading_add_nonLoading ht n hlife]
  exact Nat.add_le_add hloading (nonLoadingCount_le_four_of_source_const ht hconst hlife)

/-- **Theorem 66.2, termination bound.**  If every source-constant
lifecycle-only interval has at most `len n` loading steps on `n`, then every
lifecycle-only trace has the global bound
`countFor ht n ≤ (len n + 4) * (targetTurns ht n + 1)`. -/
theorem termination_bound (len : N → Nat)
    (hinterval : ∀ {s t : State N K E V} (ht : StepTrace s t) {n : N} {v : Option (K → Option N)},
      SourceTargetConst ht n v →
      StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht →
      loadingCount ht n ≤ len n) :
    ∀ {s t : State N K E V} (ht : StepTrace s t),
      StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht →
      ∀ n : N, countFor ht n ≤ (len n + 4) * (targetTurns ht n + 1) := by
  intro s t ht hlife n
  have hB : ∀ {s' t' : State N K E V} (ht' : StepTrace s' t') {v : Option (K → Option N)},
      SourceTargetConst ht' n v →
      StepTrace.AllSteps (fun {s} (st : Step s) => Full.StepKind.isLifecycle st.kind) ht' →
      countFor ht' n ≤ len n + 4 := by
    intro s' t' ht' v hconst hlife'
    exact countFor_le_len_add_four_of_source_const len ht' hconst hlife'
      (hinterval (n := n) (v := v) ht' hconst hlife')
  exact countFor_le_mul_of_interval_bound_of_lifecycle (len n + 4) n hB ht hlife

end StepTrace

end -- noncomputable section

end Cordix
