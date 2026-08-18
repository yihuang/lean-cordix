import LeanCordix.Coeffect

/-!
# Cordix — Faithful full-context type (bottom layer)

The paper's iterator runs against the full unified context `Γ∞`: the ambient
remainder together with the coeffect context read off the active tables.
This module defines that faithful context type at the bottom of the import
graph so that `FullCalculus` and later modules can use it without cycles.

`FullCtx K V = CoefCtx K V × CoefCtx K V`
- `FullCtx.ambient` — the part of the context no fiber's table names;
- `FullCtx.sigma` — `Σ_γ`, the union of the active fibers' tables (Eq. 40).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Full

universe u

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

end Full

end Cordix
