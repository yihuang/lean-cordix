import LeanCordix.FullCtx
import LeanCordix.Global

/-!
# Cordix — Faithful full-context layer for iterator recovery

This module builds on the bottom-layer `FullCtx` type and connects it to the
current `State` model:

* `State.fullCtx` reads the full context of a state as `(ambient, sigmaOf)`;
* `State.recoverFull` is the faithful state-level recovery operation once
  iterators are migrated to `FullCtx`.

The existing `Iterator (CoefCtx K V) E` model can be migrated incrementally
to `Iterator (FullCtx K V) E`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- Read the full context of a state: the ambient remainder paired with the
coeffect context of the active tables. -/
def State.fullCtx (s : State N K E V) : FullCtx K V :=
  (s.ambient, Full.sigmaOf s.reg)

/-- The ambient component of `State.fullCtx` is the state's ambient. -/
theorem State.fullCtx_ambient (s : State N K E V) :
    (State.fullCtx s).1 = s.ambient := rfl

/-- The coeffect component of `State.fullCtx` is `sigmaOf`. -/
theorem State.fullCtx_sigma (s : State N K E V) :
    (State.fullCtx s).2 = Full.sigmaOf s.reg := rfl

/-- The faithful reading of `State.recoverAcc`: applying the full-context
accumulator `κ : FullCtx → FullCtx` to the full context of a state.  This is
the analogue of the paper's `κ_n(s)` once iterators are migrated to
`FullCtx`. -/
def State.recoverFull (s : State N K E V) (n : N)
    (κ : FullCtx K V → FullCtx K V) : FullCtx K V :=
  κ (State.fullCtx s)

end Full

end Cordix
