import LeanCordix.Basic
import LeanCordix.StepKind

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Faithful type-level step records -/

/-- The faithful analogue of `Full.Step`: a step record whose iterator runs
on `State.fullCtx` (ambient + sigma) and whose accumulator is a
`FullCtx → FullCtx` map. -/
inductive Step (s : State N K E V) : Type (max 1 u) where
  | oInsert (n : N) (c : Component K V E) (p : Option N)
      (hn : lookup s.reg n = none)
      (hp : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f)
      (hdisj : ∀ n' f, lookup s.reg n' = some f →
        (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
      Step s
  | oRetire (n : N) (f : Fiber N K V E)
      (hf : lookup s.reg n = some f) :
      Step s
  | oRemove (n : N) (f : Fiber N K V E) (o : Option E)
      (hf : lookup s.reg n = some f) (hl : f.lc = .inactive o)
      (hchild : ∀ n' f', lookup s.reg n' = some f' → f'.parent ≠ some n) :
      Step s
  | lBegin (n : N) (f : Fiber N K V E) (v : K → Option N)
      (hf : lookup s.reg n = some f) (hl : f.lc = .inactive none)
      (ht : targetOf s.reg n = some v)
      (htable : f.table = fun _ => none) :
      Step s
  | lIter (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (ι' : Iterator (Ctx K V) E)
      (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n = some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, some ι')) :
      Step s
  | lFinish (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n = some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, none)) :
      Step s
  | lRaise (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (e : E)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (hstep : Iterator.step ι (State.fullCtx s) = .error e) :
      Step s
  | lDivertAbort (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n ≠ some v) :
      Step s
  | lDivertLand (n : N) (f : Fiber N K V E)
      (ι : Iterator (Ctx K V) E) (κ : Ctx K V → Ctx K V)
      (v : K → Option N) (δ : Ctx K V) (h : Ctx K V → Ctx K V)
      (c : Option (Iterator (Ctx K V) E))
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : targetOf s.reg n ≠ some v)
      (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, c)) :
      Step s
  | lLeave (n : N) (f : Fiber N K V E)
      (κ : Ctx K V → Ctx K V) (v : K → Option N)
      (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v)
      (ht : targetOf s.reg n ≠ some v) :
      Step s
  | lUnload (n : N) (f : Fiber N K V E)
      (κ : Ctx K V → Ctx K V) (v : K → Option N) (o : Option E)
      (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o)
      (hg : ¬ relied s.reg n) :
      Step s

namespace Step

variable {s : State N K E V}

/-- The name the step acts on. -/
def name : Step s → N
  | oInsert n .. => n
  | oRetire n .. => n
  | oRemove n .. => n
  | lBegin n .. => n
  | lIter n .. => n
  | lFinish n .. => n
  | lRaise n .. => n
  | lDivertAbort n .. => n
  | lDivertLand n .. => n
  | lLeave n .. => n
  | lUnload n .. => n

/-- The rule kind of the step. -/
def kind : Step s → Full.StepKind
  | oInsert .. => Full.StepKind.oInsert
  | oRetire .. => Full.StepKind.oRetire
  | oRemove .. => Full.StepKind.oRemove
  | lBegin .. => Full.StepKind.lBegin
  | lIter .. => Full.StepKind.lIter
  | lFinish .. => Full.StepKind.lFinish
  | lRaise .. => Full.StepKind.lRaise
  | lDivertAbort .. => Full.StepKind.lDivertAbort
  | lDivertLand .. => Full.StepKind.lDivertLand
  | lLeave .. => Full.StepKind.lLeave
  | lUnload .. => Full.StepKind.lUnload

/-- The state map `Ψ`: writes the sigma component into the acting fiber's
table, the ambient component into the ambient context, applies the
accumulator at `L-Unload`, and is the identity elsewhere. -/
def psi : Step s → State N K E V → State N K E V
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match Iterator.step ι (State.fullCtx x) with
      | .ok (δ', _, _) => State.writeEffect x n δ'
      | .error _ => x
  | lUnload n f κ v o hf hl hg, x =>
      match lookup x.reg n with
      | some g => State.writeEffect x n (κ (State.fullCtx x))
      | none => x
  | _, x => x

/-- The edit `edit`: writes only control fields, exactly as in the current
model but with full-context accumulators. -/
def edit : Step s → State N K E V → State N K E V
  | oInsert n c p hn hp hdisj, x =>
      ⟨set x.reg n ⟨c, p, fun _ => none, false, .inactive none⟩, x.ambient⟩
  | oRetire n f hf, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with retired := true }, x.ambient⟩
      | none => x
  | oRemove n f o hf hl hchild, x =>
      ⟨del x.reg n, x.ambient⟩
  | lBegin n f v hf hl ht htable, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .loading g.comp.iter id v }, x.ambient⟩
      | none => x
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .loading ι' (κ ∘ h) v }, x.ambient⟩
      | none => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .active (κ ∘ h) v }, x.ambient⟩
      | none => x
  | lRaise n f ι κ v e hreach hf hl hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v (some e) }, x.ambient⟩
      | none => x
  | lDivertAbort n f ι κ v hreach hf hl ht, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v none }, x.ambient⟩
      | none => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading (κ ∘ h) v none }, x.ambient⟩
      | none => x
  | lLeave n f κ v hf hl ht, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .unloading κ v none }, x.ambient⟩
      | none => x
  | lUnload n f κ v o hf hl hg, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with lc := .inactive o }, x.ambient⟩
      | none => x

/-- The state reached by the step. -/
def next (st : Step s) : State N K E V := edit st (psi st s)

/-- **Faithful Equation (52).** Every step factors as `s' = edit (Ψ s)`. -/
theorem factorization (st : Step s) : next st = edit st (psi st s) := rfl

/-- A step's `Ψ` effect is confined to the fiber it acts on: iterator steps
are confined to their yielded `δ`, and `L-Unload` is confined to the result
of the accumulator. -/
def Confined : Step s → Prop
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep => ConfinedEffect s n δ
  | lFinish n f ι κ v δ h hreach hf hl ht hstep => ConfinedEffect s n δ
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep => ConfinedEffect s n δ
  | lUnload n f κ v o hf hl hg => ConfinedEffect s n (κ (State.fullCtx s))
  | _ => True

/-- A step's recomputed `Ψ` is confined at both `x` and `y`.  This is the
state-pair version of `Confined` needed when `Step.psi` is evaluated away
from the step's source state. -/
def PsiConfinedAt (st : Step s) (x y : State N K E V) : Prop :=
  match st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      ∀ δ', (∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c')) →
            (∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c')) →
            ConfinedEffect x n δ' ∧ ConfinedEffect y n δ'
  | lUnload n f κ v o hf hl hg =>
      ConfinedEffect x n (κ (State.fullCtx x)) ∧
      ConfinedEffect y n (κ (State.fullCtx y))
  | _ => True

/-- `Step.psi` preserves duplicate-free names. -/
theorem psi_preserves_nodupKeys {s x : State N K E V} (st : Step s)
    (hn : NodupKeys x.reg) : NodupKeys (Step.psi st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj => simpa [Step.psi] using hn
  | oRetire n f hf => simpa [Step.psi] using hn
  | oRemove n f o hf hl hchild => simpa [Step.psi] using hn
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using hn
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using hn
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using hn
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hn
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          simpa [Step.psi, hstep_x] using State.writeEffect_preserves_nodupKeys hn
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using hn
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.psi, hg] using State.writeEffect_preserves_nodupKeys hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.psi, hn'] using hn

/-- `Step.edit` preserves duplicate-free names. -/
theorem edit_preserves_nodupKeys {s x : State N K E V} (st : Step s)
    (hn : NodupKeys x.reg) : NodupKeys (Step.edit st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj =>
      simpa [Step.edit] using nodupKeys_set x.reg n
        (Fiber.mk c p (fun _ => none) false (.inactive none)) hn
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n { g with retired := true } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | oRemove n f o hf hl hchild =>
      simpa [Step.edit] using nodupKeys_del hn n
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .loading g.comp.iter id v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .loading ι' (κ ∘ h) v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .active (κ ∘ h) v } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v (some e) } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading (κ ∘ h) v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .unloading κ v none } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using nodupKeys_set x.reg n
          { g with lc := .inactive o } hn
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hn

/-- `Step.psi` preserves pairwise disjointness of tables, assuming the
recomputed effect is confined at the input state. -/
theorem psi_preserves_pairwiseDisjointTables {s x : State N K E V} (st : Step s)
    (hnodup : NodupKeys x.reg) (hdisj : PairwiseDisjointTables x.reg)
    (hconf : Step.PsiConfinedAt st x x) :
    PairwiseDisjointTables (Step.psi st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj0 => simpa [Step.psi] using hdisj
  | oRetire n f hf => simpa [Step.psi] using hdisj
  | oRemove n f o hf hl hchild => simpa [Step.psi] using hdisj
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using hdisj
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using hdisj
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using hdisj
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simpa [Step.psi, hstep_x] using hdisj
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          have hconf' := hconf δ' ⟨h', c', hstep_x⟩ ⟨h', c', hstep_x⟩
          simpa [Step.psi, hstep_x] using
            State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using hdisj
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        have hconf' := hconf
        simpa [Step.psi, hg] using
          State.writeEffect_preserves_pairwiseDisjointTables hnodup hdisj hconf'.1
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.psi, hn'] using hdisj

/-- `Step.edit` preserves pairwise disjointness of tables. -/
theorem edit_preserves_pairwiseDisjointTables {s x : State N K E V} (st : Step s)
    (hnodup : NodupKeys x.reg) (hdisj : PairwiseDisjointTables x.reg) :
    PairwiseDisjointTables (Step.edit st x).reg := by
  cases st with
  | oInsert n c p hn0 hp hdisj0 =>
      simpa [Step.edit] using pairwiseDisjointTables_set_empty hnodup hdisj
        (g := Fiber.mk c p (fun _ => none) false (.inactive none)) rfl
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with retired := true }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | oRemove n f o hf hl hchild =>
      simpa [Step.edit] using pairwiseDisjointTables_del hdisj n
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .loading g.comp.iter id v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .loading ι' (κ ∘ h) v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .active (κ ∘ h) v }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v (some e) }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading (κ ∘ h) v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .unloading κ v none }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simpa [Step.edit, hg] using
          pairwiseDisjointTables_set_preserves_table hnodup hdisj hg
            (new := { g with lc := .inactive o }) rfl
      · have hn' : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simpa [Step.edit, hn'] using hdisj

/-- `Step.psi` never changes the lookup at a different name. -/
theorem psi_preserves_lookup_ne {s x : State N K E V} (st : Step s) {m : N}
    (hm : m ≠ st.name) : lookup (Step.psi st x).reg m = lookup x.reg m := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.psi]
  | oRetire n f hf => simp [Step.psi]
  | oRemove n f o hf hl hchild => simp [Step.psi]
  | lBegin n f v hf hl ht htable => simp [Step.psi]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.psi]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.psi]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e => simp [Step.psi, hstep_x]
      | ok p =>
          rcases p with ⟨δ', h', c'⟩
          by_cases hx : (lookup x.reg n).isSome
          · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
            simp [Step.psi, hstep_x, hg]
            unfold State.writeEffect
            rw [hg]
            exact lookup_set_ne x.reg n m { g with table := splitTable g.comp.prov δ'.2 } hm'
          · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            simp [Step.psi, hstep_x, State.writeEffect, hn]
  | lLeave n f κ v hf hl ht => simp [Step.psi]
  | lUnload n f κ v o hf hl hg =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.psi, hg]
        unfold State.writeEffect
        rw [hg]
        exact lookup_set_ne x.reg n m
          { g with table := splitTable g.comp.prov (κ (State.fullCtx x)).2 } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.psi, State.writeEffect, hn]

/-- `Step.psi` preserves pointwise fiber agreement. -/
theorem psi_preserves_sameFiberAt {s x y : State N K E V} (st : Step s) {m : N}
    (h : SameFiberAt x y m) : SameFiberAt (Step.psi st x) (Step.psi st y) m := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi] using h
  | oRetire n f hf => simpa [Step.psi] using h
  | oRemove n f o hf hl hchild => simpa [Step.psi] using h
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using h
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using h
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using h
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e' => simpa [Step.psi, hstep_x, hstep_y] using h
          | ok p =>
              rcases p with ⟨δ', h'', c'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_right (n := n) (δ := δ') h)
      | ok p =>
          rcases p with ⟨δx, hx', cx'⟩
          cases hstep_y : Iterator.step ι (State.fullCtx y) with
          | error e =>
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt_left (n := n) (δ := δx) h)
          | ok q =>
              rcases q with ⟨δy, hy', cy'⟩
              simpa [Step.psi, hstep_x, hstep_y] using
                (State.writeEffect_preserves_sameFiberAt (n := n) (δx := δx) (δy := δy) h)
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using h
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
        by_cases hy : (lookup y.reg n).isSome
        · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          simp [Step.psi, hgx, hgy]
          exact State.writeEffect_preserves_sameFiberAt (n := n)
            (δx := κ (State.fullCtx x)) (δy := κ (State.fullCtx y)) h
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.psi, hgx, hyn]
          exact State.writeEffect_preserves_sameFiberAt_left (n := n)
            (δ := κ (State.fullCtx x)) h
      · have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        by_cases hy : (lookup y.reg n).isSome
        · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          simp [Step.psi, hxn, hgy]
          exact State.writeEffect_preserves_sameFiberAt_right (n := n)
            (δ := κ (State.fullCtx y)) h
        · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.psi, hxn, hyn]
          exact h

/-- `Step.edit` never changes the lookup at a different name. -/
theorem edit_preserves_lookup_ne {s x : State N K E V} (st : Step s) {m : N}
    (hm : m ≠ st.name) : lookup (Step.edit st x).reg m = lookup x.reg m := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      simp [Step.edit]
      exact lookup_set_ne x.reg n m (Fiber.mk c p (fun _ => none) false (.inactive none)) hm'
  | oRetire n f hf =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with retired := true } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | oRemove n f o hf hl hchild =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      simp [Step.edit]
      exact lookup_del_ne (r := x.reg) (n := n) (m := m) hm'
  | lBegin n f v hf hl ht htable =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .loading g.comp.iter id v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .loading ι' (κ ∘ h) v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .active (κ ∘ h) v } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v (some e) } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading (κ ∘ h) v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lLeave n f κ v hf hl ht =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .unloading κ v none } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]
  | lUnload n f κ v o hf hl hg =>
      have hm' : m ≠ n := by simpa [Step.name] using hm
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        simp [Step.edit, hg]
        exact lookup_set_ne x.reg n m { g with lc := .inactive o } hm'
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        simp [Step.edit, hn]

/-- `Step.edit` preserves pointwise fiber agreement. -/
theorem edit_preserves_sameFiberAt {s x y : State N K E V} (st : Step s) {m : N}
    (h : SameFiberAt x y m) : SameFiberAt (Step.edit st x) (Step.edit st y) m := by
  by_cases hmn : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj =>
        simpa [Step.edit] using set_preserves_sameFiberAt (n := n)
          (g := Fiber.mk c p (fun _ => none) false (.inactive none)) h
    | oRetire n f hf =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with retired := true }) (gy := { gy with retired := true }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | oRemove n f o hf hl hchild =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        simp [Step.edit, lookup_del_self]
    | lBegin n f v hf hl ht htable =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .loading gx.comp.iter id v })
            (gy := { gy with lc := .loading gy.comp.iter id v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .loading ι' (κ ∘ hh) v })
            (gy := { gy with lc := .loading ι' (κ ∘ hh) v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .active (κ ∘ hh) v })
            (gy := { gy with lc := .active (κ ∘ hh) v }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lRaise n f ι κ v e hreach hf hl hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v (some e) })
            (gy := { gy with lc := .unloading κ v (some e) }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lDivertAbort n f ι κ v hreach hf hl ht =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v none })
            (gy := { gy with lc := .unloading κ v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading (κ ∘ hh) v none })
            (gy := { gy with lc := .unloading (κ ∘ hh) v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lLeave n f κ v hf hl ht =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .unloading κ v none })
            (gy := { gy with lc := .unloading κ v none }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
    | lUnload n f κ v o hf hl hg =>
        unfold SameFiberAt
        simp [Step.name] at h ⊢
        by_cases hx : (lookup x.reg n).isSome
        · have hy : (lookup y.reg n).isSome := by
            unfold SameFiberAt at h
            rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
            rw [hgx] at h
            by_cases hy' : (lookup y.reg n).isSome
            · exact hy'
            · have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy'
              simp [hyn] at h
          rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
          rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
          have hprov : gx.comp.prov = gy.comp.prov := by
            unfold SameFiberAt at h
            rw [hgx, hgy] at h
            exact h
          simp [Step.edit, hgx, hgy]
          exact set_preserves_sameFiberAt_of_prov (n := n)
            (gx := { gx with lc := .inactive o })
            (gy := { gy with lc := .inactive o }) h hprov
        · have hy : ¬ (lookup y.reg n).isSome := by
            intro hy
            unfold SameFiberAt at h
            have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
            rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
            simp [hxn, hgy] at h
          have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
          have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
          simp [Step.edit, hxn, hyn]
  · have hx_lookup : lookup (Step.edit st x).reg m = lookup x.reg m :=
      Step.edit_preserves_lookup_ne st hmn
    have hy_lookup : lookup (Step.edit st y).reg m = lookup y.reg m :=
      Step.edit_preserves_lookup_ne st hmn
    unfold SameFiberAt
    rw [hx_lookup, hy_lookup]
    exact h

/-- For a non-insert, non-remove step, `edit` agrees with the input state at
the acting name up to `SameFiberAt`. -/
theorem edit_preserves_sameFiberAt_self_of_not_insert_remove {s x : State N K E V}
    (st : Step s) (hno_insert : st.kind ≠ Full.StepKind.oInsert)
    (hno_remove : st.kind ≠ Full.StepKind.oRemove) :
    SameFiberAt (Step.edit st x) x st.name := by
  cases st with
  | oInsert n c p hn hp hdisj => exact False.elim (hno_insert (by simp [Step.kind]))
  | oRetire n f hf =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | oRemove n f o hf hl hchild => exact False.elim (hno_remove (by simp [Step.kind]))
  | lBegin n f v hf hl ht htable =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lLeave n f κ v hf hl ht =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]
  | lUnload n f κ v o hf hl hg =>
      by_cases hx : (lookup x.reg n).isSome
      · rcases Option.isSome_iff_exists.mp hx with ⟨g, hg⟩
        unfold SameFiberAt
        simp [Step.edit, Step.name, hg, lookup_set_eq]
      · have hn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        unfold SameFiberAt
        simp [Step.edit, Step.name, hn]

/-- If a step is confined at its source state, then `PsiConfinedAt` holds
with both arguments equal to that source state. -/
theorem psiConfinedAt_self_of_confined {s : State N K E V} (st : Step s)
    (hconf : Step.Confined st) : Step.PsiConfinedAt st s s := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hδ : δ = δ' := by
        rw [hstep] at hx
        injection hx with hpair
        injection hpair with hδ
      subst δ'
      exact ⟨hconf, hconf⟩
  | lUnload n f κ v o hf hl hg =>
      simpa [Step.Confined, Step.PsiConfinedAt] using hconf
  | _ => trivial

/-- If `PsiConfinedAt` holds for a pair with equal full contexts, it also
holds for the left state paired with itself. -/
theorem psiConfinedAt_self_of_pair_left {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hconf : Step.PsiConfinedAt st x y) : Step.PsiConfinedAt st x x := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hy' : ∃ h' c', Iterator.step ι (State.fullCtx y) = .ok (δ', h', c') := by
        exact ⟨h', c', by rwa [← hfull]⟩
      exact ⟨(hconf δ' ⟨h', c', hx⟩ hy').1, (hconf δ' ⟨h', c', hx⟩ hy').1⟩
  | lUnload n f κ v o hf hl hg =>
      exact ⟨hconf.1, hconf.1⟩
  | _ => trivial

/-- If `PsiConfinedAt` holds for a pair with equal full contexts, it also
holds for the right state paired with itself. -/
theorem psiConfinedAt_self_of_pair_right {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hconf : Step.PsiConfinedAt st x y) : Step.PsiConfinedAt st y y := by
  cases st with
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      have hx' : ∃ h' c', Iterator.step ι (State.fullCtx x) = .ok (δ', h', c') := by
        exact ⟨h', c', by simpa [hfull] using hx⟩
      exact ⟨(hconf δ' hx' ⟨h', c', hx⟩).2, (hconf δ' hx' ⟨h', c', hx⟩).2⟩
  | lUnload n f κ v o hf hl hg =>
      exact ⟨hconf.2, hconf.2⟩
  | _ => trivial

/-- `Step.next` preserves duplicate-free names. -/
theorem next_preserves_nodupKeys {s : State N K E V} (st : Step s)
    (hn : NodupKeys s.reg) : NodupKeys (Step.next st).reg := by
  rw [Step.factorization]
  exact Step.edit_preserves_nodupKeys st (Step.psi_preserves_nodupKeys st hn)

/-- `Step.next` preserves pairwise disjointness of tables, provided the
step's `Ψ` effect is confined at the source state. -/
theorem next_preserves_pairwiseDisjointTables {s : State N K E V} (st : Step s)
    (hnodup : NodupKeys s.reg) (hdisj : PairwiseDisjointTables s.reg)
    (hconf : Step.Confined st) : PairwiseDisjointTables (Step.next st).reg := by
  rw [Step.factorization]
  exact Step.edit_preserves_pairwiseDisjointTables st
    (Step.psi_preserves_nodupKeys st hnodup)
    (Step.psi_preserves_pairwiseDisjointTables st hnodup hdisj
      (Step.psiConfinedAt_self_of_confined st hconf))

end Step

end Cordix
