import LeanCordix.Global

/-!
# Cordix — Faithful full-context layer for iterator recovery

This module starts the model extension that makes recovery exactness faithful
to the paper.  In the paper the iterator `ι : Γ∞ → ...` runs against the full
unified context `Γ∞`: the ambient remainder together with the coeffect
context read off the active tables.  The current formalization passes only
`Full.sigmaOf s.reg` to `Iterator.step`, so an inverse `h` cannot recover the
ambient part of the state.

Here we introduce the faithful context type

`FullCtx K V = CoefCtx K V × CoefCtx K V`

where the first component is the ambient remainder and the second is the
union of active tables (`Σ_γ`).  A faithful iterator is then
`Iterator (FullCtx K V) E`.  The existing `Iterator (CoefCtx K V) E` model
can be migrated incrementally to this type.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- **Faithful full context.** `(ambient, sigma)` where `ambient` is the part
of the context no fiber table names and `sigma` is the union of the active
fibers' tables (`Σ_γ`, Eq. 40). -/
abbrev FullCtx (K : Type) (V : K → Type u) : Type _ :=
  CoefCtx K V × CoefCtx K V

namespace FullCtx

/-- The ambient component of a full context. -/
abbrev ambient {K : Type} {V : K → Type u} (γ : FullCtx K V) : CoefCtx K V :=
  γ.1

/-- The coeffect component (`Σ_γ`) of a full context. -/
abbrev sigma {K : Type} {V : K → Type u} (γ : FullCtx K V) : CoefCtx K V :=
  γ.2

end FullCtx

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
