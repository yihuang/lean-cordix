/-!
# LeanCordix.StepKind — shared step-kind names

The ten rule names used by both the legacy trace model and the canonical
faithful model.  Kept as a tiny standalone module so the faithful model does
not depend on the old full-calculus/global metatheory.
-/

namespace Cordix

namespace Full

/-- The ten rule names, as data. -/
inductive StepKind
  | oInsert
  | oRetire
  | oRemove
  | lBegin
  | lIter
  | lFinish
  | lRaise
  | lDivertAbort
  | lDivertLand
  | lLeave
  | lUnload
  deriving DecidableEq, Repr

namespace StepKind

/-- A lifecycle kind. -/
def isLifecycle : StepKind → Prop
  | oInsert | oRetire | oRemove => False
  | lBegin | lIter | lFinish | lRaise | lDivertAbort | lDivertLand | lLeave | lUnload => True

/-- A kind whose `Ψ` writes the acting fiber's table. -/
def writesTable : StepKind → Prop
  | lIter | lFinish | lDivertLand => True
  | _ => False

/-- A kind whose `Ψ` is the acting fiber's accumulator. -/
def appliesAcc : StepKind → Prop
  | lUnload => True
  | _ => False

end StepKind

end Full

end Cordix
