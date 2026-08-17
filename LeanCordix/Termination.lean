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
provides the basic recursive definitions and their immediate computation
lemmas.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

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

end Step.StepTrace

end Full

end Cordix
