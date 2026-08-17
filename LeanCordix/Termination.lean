import LeanCordix.Global

/-!
# Cordix — Section 4.4.4: Termination scaffolding (Theorem 66.2)

This module starts the termination part of Theorem 66.  It introduces the
numerical quantities used in the paper's termination proof:

* `Step.StepTrace.length` — the number of steps in a trace;
* `Step.StepTrace.countFor` — the number of steps acting on a given fiber;
* `Step.StepTrace.targetTurns` — the number of times a fiber's target view
  changes along a trace (Eq. 61).

The eventual goal is the bound
`countFor ht n ≤ (len n + 4) * (targetTurns ht n + 1)`
and finiteness of the total number of lifecycle steps.  This file currently
provides the basic recursive definitions, their immediate computation
lemmas, and the combinatorial half of the bound: if every source-constant
target interval has at most `B` steps acting on `n`, then
`countFor ht n ≤ B * (targetTurns ht n + 1)`.

The per-interval bound `B = len n + 4` is the remaining part of the paper's
termination proof.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

noncomputable section
open Classical

namespace Step.StepTrace

/-- The number of steps in a type-level trace. -/
def length {s t : State N K E V} (ht : Step.StepTrace s t) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons _ _ ht => 1 + length ht

/-- The number of steps in a trace that act on a particular name. -/
def countFor {s t : State N K E V} (ht : Step.StepTrace s t) (n : N) : Nat :=
  match ht with
  | .nil _ => 0
  | .cons st _ ht =>
      (if st.name = n then 1 else 0) + countFor ht n

/-- The number of times a fiber's target view changes along a trace,
Eq. (61). -/
noncomputable def targetTurns {s t : State N K E V} (ht : Step.StepTrace s t) (n : N) : Nat := by
  classical
  exact
    match ht with
    | .nil _ => 0
    | .cons st _ ht =>
        (if Full.targetOf s.reg n ≠ Full.targetOf (Step.next st).reg n then 1 else 0) +
          targetTurns ht n

@[simp] theorem length_nil (s : State N K E V) :
    length (Step.StepTrace.nil s) = 0 := rfl

@[simp] theorem length_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : Step.StepTrace s₂ s₃) :
    length (Step.StepTrace.cons st hnext ht) = 1 + length ht := rfl

@[simp] theorem countFor_nil (s : State N K E V) (n : N) :
    countFor (Step.StepTrace.nil s) n = 0 := rfl

@[simp] theorem countFor_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : Step.StepTrace s₂ s₃) (n : N) :
    countFor (Step.StepTrace.cons st hnext ht) n =
      (if st.name = n then 1 else 0) + countFor ht n := rfl

@[simp] theorem targetTurns_nil (s : State N K E V) (n : N) :
    targetTurns (Step.StepTrace.nil s) n = 0 := by
  simp [targetTurns]

/-- Every step counted by `countFor` acts on `n`; if no step acts on `n`,
the count is zero. -/
theorem countFor_eq_zero_of_no_steps {s t : State N K E V}
    (ht : Step.StepTrace s t) {n : N}
    (hno : Step.StepTrace.AllSteps (fun {s} (st : Step s) => st.name ≠ n) ht) :
    countFor ht n = 0 := by
  cases ht with
  | nil s => rfl
  | cons st hnext ht =>
      rcases hno with ⟨hst, htail⟩
      have htail' : countFor ht n = 0 := countFor_eq_zero_of_no_steps ht htail
      simp [Step.StepTrace.countFor, hst, htail']

/-- The per-fiber count cannot exceed the trace length. -/
theorem countFor_le_length {s t : State N K E V} (ht : Step.StepTrace s t) (n : N) :
    countFor ht n ≤ length ht := by
  induction ht with
  | nil s => simp [Step.StepTrace.countFor, Step.StepTrace.length]
  | cons st hnext ht ih =>
      by_cases hname : st.name = n
      · simp [Step.StepTrace.countFor, Step.StepTrace.length, hname, ih]
      · simp [Step.StepTrace.countFor, Step.StepTrace.length, hname, ih]
        omega

@[simp] theorem targetTurns_cons {s₁ s₂ s₃ : State N K E V}
    (st : Step s₁) (hnext : Step.next st = s₂) (ht : Step.StepTrace s₂ s₃) (n : N) :
    targetTurns (Step.StepTrace.cons st hnext ht) n =
      (if Full.targetOf s₁.reg n ≠ Full.targetOf (Step.next st).reg n then 1 else 0) +
        targetTurns ht n := by
  classical
  simp [targetTurns, hnext]

/-- The number of target turns cannot exceed the trace length. -/
theorem targetTurns_le_length {s t : State N K E V}
    (ht : Step.StepTrace s t) (n : N) :
    targetTurns ht n ≤ length ht := by
  classical
  induction ht with
  | nil s => simp [targetTurns, length]
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      simp [targetTurns, length, ih]
      by_cases h : Full.targetOf s₁.reg n = Full.targetOf (Step.next st).reg n
      · simp [h]
        omega
      · simp [h]
        omega

/-! ## Interval splitting and the global counting bound

The paper's termination proof (A) bounds the number of `n`-steps in each
maximal interval on which `targetOf _ n` is constant.  The material below
formalizes the combinatorial half of Theorem 66.2: if every such interval
has at most `B` steps acting on `n`, then the whole trace satisfies
`countFor ht n ≤ B * (targetTurns ht n + 1)`.

The interval bound itself is supplied as the hypothesis `hB`; the paper's
`len` assumption is one way to instantiate it with `B = len n + 4`.
-/

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
  | .cons st _ ht => Full.targetOf s.reg n = v ∧ SourceTargetConst ht n v

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
  source_const : SourceTargetConst pre n (Full.targetOf s.reg n)
  post_len_le : length post ≤ length ht
  post_len_lt : (¬ IsNil post) → length post < length ht
  turns_eq : targetTurns ht n = targetTurns pre n + targetTurns post n
  pre_turns_le_one : targetTurns pre n ≤ 1
  pre_turns_eq_one_of_post : (¬ IsNil post) → targetTurns pre n = 1

/-- Split a trace at the first change of `targetOf _ n`. -/
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
      by_cases h : Full.targetOf (Step.next st).reg n = Full.targetOf s₁.reg n
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
            by_cases h2 : Full.targetOf s₁.reg n = Full.targetOf (Step.next st).reg n
            · simp [h2]
            · simp [h2],
          by
            intro _
            simp [targetTurns_cons]
            exact fun hEq => h hEq.symm⟩

/-- **Theorem 66.2, combinatorial half.**  If every interval on which
`targetOf _ n` is source-constant has at most `B` steps acting on `n`, then
`countFor ht n ≤ B * (targetTurns ht n + 1)`. -/
theorem countFor_le_mul_of_interval_bound (B : Nat) (n : N)
    (hB : ∀ {s t : State N K E V} (ht : StepTrace s t) {v : Option (K → Option N)},
      SourceTargetConst ht n v → countFor ht n ≤ B) :
    ∀ {s t : State N K E V} (ht : StepTrace s t),
      countFor ht n ≤ B * (targetTurns ht n + 1) := by
  intro s t ht
  let sp := splitFirstInterval ht n
  rcases sp with ⟨mid, pre, post, eq, source_const, post_len_le, post_len_lt, turns_eq, pre_turns_le_one, pre_turns_eq_one_of_post⟩
  have hBpre : countFor pre n ≤ B :=
    hB pre (v := Full.targetOf s.reg n) source_const
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

To instantiate the per-interval bound one still has to prove the paper's
`len` hypothesis.  A useful decomposition for that proof is to separate the
loading-phase steps (`L-Iter`, `L-Finish`, `L-Raise`, `L-Divert`) from the
boundary steps (`L-Begin`, `L-Leave`, `L-Unload`).  The lemma below is the
counting identity behind that separation for traces consisting only of
lifecycle steps. -/

/-- A loading-phase lifecycle kind: a step that can occur while the fiber
is in `loading`. -/
def IsLoadingKind (k : StepKind) : Prop :=
  k = StepKind.lIter ∨ k = StepKind.lFinish ∨ k = StepKind.lRaise ∨
    k = StepKind.lDivertAbort ∨ k = StepKind.lDivertLand

/-- A non-loading lifecycle kind: a step that opens, leaves, or closes an
activation episode. -/
def IsNonLoadingKind (k : StepKind) : Prop :=
  k = StepKind.lBegin ∨ k = StepKind.lLeave ∨ k = StepKind.lUnload

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
    (hlife : StepTrace.AllSteps (fun {s} (st : Step s) => StepKind.isLifecycle st.kind) ht) :
    countFor ht n = loadingCount ht n + nonLoadingCount ht n := by
  induction ht with
  | nil s => simp [countFor, loadingCount, nonLoadingCount]
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      rcases hlife with ⟨hlife_st, hlife_tail⟩
      have ih' := ih hlife_tail
      by_cases hname : st.name = n
      · simp [countFor, loadingCount, nonLoadingCount, hname]
        cases st <;> simp [IsLoadingKind, IsNonLoadingKind, Step.kind, StepKind.isLifecycle]
          at hlife_st ⊢ <;> omega
      · simp [countFor, loadingCount, nonLoadingCount, hname, ih']

end Step.StepTrace

end -- noncomputable section

end Full

end Cordix
