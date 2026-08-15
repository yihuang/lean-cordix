import LeanCordix.Revertible

/-!
# Cordix — Section 4.3.2/4.3.4: Effect Iterators

This module formalizes Definitions 51 and 52 of *A Programming Paradigm for
Spatiotemporal Composability*: the effect iterator, a recursive effect whose
iterations may yield a new context, an inverse, and a continuation, and may
raise an error instead (Section 4.3.4).

We keep the failure refinement from the start: the type is

`Iterator Γ E := μℑ. Γ → Except E (Γ × (Γ → Γ) × Option ℑ)`

so an iteration either raises an error `e : E` or yields a triple
`(δ, g, c)` with the new context `δ`, the inverse `g` of the iteration at the
state where it ran, and a continuation `c` (`none` for termination, `some ι`
for the next iteration).

The plain effect functions of `LeanCordix.Revertible` embed as the degenerate
one-step iterator.  We do not attempt to define the recursive lift
`effect_iter` of Definition 52 as a computable function: the calculus of
Section 4.3 only ever applies one iteration at a time, so the lift is given
here as a relation, `Lifts`, which records the state and the accumulated
inverse of a complete (successful) run.  The rules of the full calculus use
`step` directly.
-/

namespace Cordix

universe u v

/-- **Definition 51 / Eq. 49.** An effect iterator with errors: one step
runs at a context state and either raises an error or yields the next state,
the inverse of the step, and an optional continuation. -/
inductive Iterator (Γ : Type u) (E : Type v) : Type (max u v) where
  | mk (run : Γ → Except E (Γ × (Γ → Γ) × Option (Iterator Γ E)))

namespace Iterator

variable {Γ : Type u} {E : Type v}

/-- The single step of an iterator at `γ`. -/
def step (ι : Iterator Γ E) (γ : Γ) : Except E (Γ × (Γ → Γ) × Option (Iterator Γ E)) :=
  match ι with
  | ⟨run⟩ => run γ

/-- **Definition 51 / Eq. 49 (witness).** A successful iteration's yielded
inverse recovers the state the iteration ran against; a raised error has
nothing to undo and imposes no condition. -/
def Witnessed (ι : Iterator Γ E) : Prop :=
  ∀ γ, match step ι γ with
    | .ok (δ, g, _) => g δ = γ
    | .error _ => True

/-- A one-step iterator from a plain effect function. -/
def ofEff (τ : Eff Γ) : Iterator Γ E :=
  ⟨fun γ => .ok ((τ γ).1, (τ γ).2, none)⟩

/-- The embedding of `Eff` into `Iterator` preserves witnessing. -/
theorem witnessed_ofEff {τ : Eff Γ} (h : _root_.Cordix.Witnessed τ) :
    Witnessed (ofEff τ : Iterator Γ E) := by
  intro γ
  show ((τ γ).2 ((τ γ).1) = γ)
  exact h γ

/-- The forward state map of one step; the identity on the state where an
error is raised (the calculus never applies an iterator step after a raise,
so this is only a convenience). -/
def stepFwd (ι : Iterator Γ E) (γ : Γ) : Γ :=
  match step ι γ with
    | .ok (δ, _, _) => δ
    | .error _ => γ

/-- The inverse yielded by one step; `id` on an error. -/
def stepInv (ι : Iterator Γ E) (γ : Γ) : Γ → Γ :=
  match step ι γ with
    | .ok (_, g, _) => g
    | .error _ => id

/-- The continuation yielded by one step; `none` on an error. -/
def stepCont (ι : Iterator Γ E) (γ : Γ) : Option (Iterator Γ E) :=
  match step ι γ with
    | .ok (_, _, c) => c
    | .error _ => none

/-- **Definition 52** as a relation: `Lifts ι ec ec' ν` when a complete run
of the iterator `ι` starting at the effect-context state `ec` ends at `ec'`
and has accumulated the inverse `ν`.  The recursive equations of the paper
are exactly the two constructors. -/
inductive Lifts : Iterator Γ E → EffectCtx Γ → EffectCtx Γ → (EffectCtx Γ → EffectCtx Γ) → Prop
  | done {ι : Iterator Γ E} {γ : Γ} {κ : Γ → Γ} {δ : Γ} {g : Γ → Γ}
      (h : step ι γ = .ok (δ, g, none)) :
      Lifts ι (γ, κ) (δ, κ ∘ g) (track (g, stepFwd ι))
  | cont {ι ι' : Iterator Γ E} {γ : Γ} {κ : Γ → Γ} {δ : Γ} {g : Γ → Γ}
      (h : step ι γ = .ok (δ, g, some ι'))
      {ec' : EffectCtx Γ} {ν ν' : EffectCtx Γ → EffectCtx Γ}
      (hν : Lifts ι' (δ, κ ∘ g) ec' ν)
      (hcomp : ν' = ν ∘ track (g, stepFwd ι)) :
      Lifts ι (γ, κ) ec' ν'

/-- Reachability between iterators: the continuations of `ι`, recursively. -/
inductive Reachable : Iterator Γ E → Iterator Γ E → Prop
  | self (ι : Iterator Γ E) : Reachable ι ι
  | step {ι ι' ι'' : Iterator Γ E} {γ δ : Γ} {g : Γ → Γ}
      (h : step ι γ = .ok (δ, g, some ι')) (hR : Reachable ι' ι'') :
      Reachable ι ι''

/-- Every reachable continuation of the iterator is witnessed.  This is
the full `iter*` witness of Definition 51, parameterized over the whole
iterator rather than one step. -/
def WitnessedAll (ι : Iterator Γ E) : Prop :=
  ∀ {ι'}, Reachable ι ι' → Witnessed ι'

/-- The one-step witness is part of the whole-iterator witness. -/
theorem witnessed_of_witnessedAll {ι : Iterator Γ E} (w : WitnessedAll ι) : Witnessed ι :=
  w (Reachable.self ι)

/-- A witnessed one-step iterator is witnessed as a whole iterator. -/
theorem witnessedAll_ofEff {τ : Eff Γ} (h : _root_.Cordix.Witnessed τ) :
    WitnessedAll (ofEff τ : Iterator Γ E) := by
  intro ι' hR
  cases hR with
  | self ι => exact witnessed_ofEff h
  | step hstep hR => cases hstep

/-- **Definition 52 / Theorem 16 for iterators.** A complete successful run
of a witnessed iterator leaves the soundness invariant unchanged. -/
theorem soundness_lifts {ι : Iterator Γ E} (w : WitnessedAll ι)
    {ec ec' : EffectCtx Γ} {ν : EffectCtx Γ → EffectCtx Γ}
    (h : Lifts ι ec ec' ν) : soundness ec' = soundness ec := by
  induction h with
  | @done ι γ κ δ g hstep =>
      have hg : g δ = γ := by
        have := witnessed_of_witnessedAll w γ
        unfold Witnessed at this
        rw [hstep] at this
        exact this
      simp [soundness, hg]
  | @cont ι ι' γ κ δ g hstep ec' ν ν' hν hcomp ih =>
      have hg : g δ = γ := by
        have := witnessed_of_witnessedAll w γ
        unfold Witnessed at this
        rw [hstep] at this
        exact this
      have w' : WitnessedAll ι' := by
        intro ι'' hR
        exact w (Reachable.step hstep hR)
      have ih' := ih w'
      calc
        soundness ec' = soundness (δ, κ ∘ g) := ih'
        _ = soundness (γ, κ) := by
          simp [soundness, hg]

end Iterator

end Cordix
