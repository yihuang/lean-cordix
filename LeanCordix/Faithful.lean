import LeanCordix.FullCtx
import LeanCordix.Iterator
import LeanCordix.Coeffect
import LeanCordix.TraceModel

/-!
# Cordix — Faithful full-context model (parallel development)

This module is the faithful counterpart of `FullCalculus` / `TraceModel`:
iterators run against the full context `FullCtx = (ambient, sigma)` rather
than against `sigmaOf` alone.  It is intentionally developed in parallel so
the existing model stays green while the faithful definitions and theorems
are built out.

Current contents:

* `Faithful.Component` — component with `Iterator (FullCtx K V) E`;
* `Faithful.Lifecycle` — lifecycle carrying `FullCtx → FullCtx` accumulators;
* `Faithful.Fiber`, `Faithful.Registry`, `Faithful.State`;
* the derived context operations `sigmaOf`, `providerOf`, `targetOf`,
  `quiet`, `relied`, and `State.fullCtx`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

namespace Faithful

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- The faithful iterator context: `(ambient, sigma)`. -/
abbrev Ctx (K : Type) (V : K → Type u) : Type _ :=
  Full.FullCtx K V

/-- **Faithful Definition 43.** A component whose effect iterator runs on the
full context. -/
structure Component (K : Type) (V : K → Type u) (E : Type) where
  /-- The dependencies required from the environment. -/
  spec : Spec K
  /-- The keys the component may provide. -/
  prov : List K
  /-- The effect iterator executed on activation. -/
  iter : Iterator (Ctx K V) E
  /-- The iterator is witnessed. -/
  wit : Iterator.Witnessed iter

/-- **Faithful Definition 49.** Lifecycle states with full-context
accumulators. -/
inductive Lifecycle (N : Type) (K : Type) (V : K → Type u) (E : Type)
  | inactive (outcome : Option E) : Lifecycle N K V E
  | loading (iter : Iterator (Ctx K V) E) (acc : Ctx K V → Ctx K V)
      (view : K → Option N) : Lifecycle N K V E
  | active (acc : Ctx K V → Ctx K V) (view : K → Option N) :
      Lifecycle N K V E
  | unloading (acc : Ctx K V → Ctx K V) (view : K → Option N)
      (outcome : Option E) : Lifecycle N K V E

namespace Lifecycle

/-- A fiber is installed when it is not inactive. -/
def installed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive _ => False
  | .loading _ _ _ => True
  | .active _ _ => True
  | .unloading _ _ _ => True

/-- The committed view of a lifecycle state. -/
def viewOf {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → K → Option N
  | .inactive _ => fun _ => none
  | .loading _ _ v => v
  | .active _ v => v
  | .unloading _ v _ => v

/-- A fiber is failed when it has reached an error outcome. -/
def failed {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Prop
  | .inactive (some _) => True
  | _ => False

/-- The accumulator carried by a lifecycle state; `id` for inactive. -/
def acc {N K : Type} {V : K → Type u} {E : Type} :
    Lifecycle N K V E → Ctx K V → Ctx K V
  | .inactive _ => id
  | .loading _ κ _ => κ
  | .active κ _ => κ
  | .unloading κ _ _ => κ

end Lifecycle

/-- **Faithful Definition 44.** A fiber in the faithful model. -/
structure Fiber (N : Type) (K : Type) (V : K → Type u) (E : Type) where
  comp : Component K V E
  parent : Option N
  table : CoefCtx K V
  retired : Bool
  lc : Lifecycle N K V E

/-- **Faithful Definition 45.** The registry: a list of named fibers. -/
abbrev Registry (N K : Type) (V : K → Type u) (E : Type) :=
  List (N × Fiber N K V E)

/-- Lookup in a registry. -/
def lookup {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Option (Fiber N K V E)
  | [], _ => none
  | p :: rest, n => if p.1 = n then some p.2 else lookup rest n

/-- Pointwise update. -/
def set {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Fiber N K V E → Registry N K V E
  | [], n, f => [(n, f)]
  | p :: rest, n, f =>
      if p.1 = n then (n, f) :: rest else p :: set rest n f

/-- Removal. -/
def del {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type} :
    Registry N K V E → N → Registry N K V E
  | [], _ => []
  | p :: rest, n => if p.1 = n then del rest n else p :: del rest n

/-- The coeffect context of a state: the union of the tables of active
fibers. -/
def sigmaOf {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) : CoefCtx K V :=
  fun k => r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => p.2.table k <|> acc
    | _ => acc

/-- The provider of a key: the active fiber whose table defines it. -/
def providerOf {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (k : K) : Option N :=
  r.foldr (init := none) fun p acc =>
    match p.2.lc with
    | .active _ _ => if (p.2.table k).isSome then some p.1 else acc
    | _ => acc

/-- The target view of `n` at `r`. -/
noncomputable def targetOf {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type} (r : Registry N K V E) (n : N) : Option (K → Option N) :=
  match lookup r n with
  | some f =>
      if f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec then none
      else some (fun k => if k ∈ f.comp.spec then providerOf r k else none)
  | none => none

/-- Quiescence in the faithful model. -/
def quiet {N : Type} [DecidableEq N] {K : Type} [DecidableEq K] {V : K → Type u}
    {E : Type} (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f →
    match f.lc with
    | .inactive o => o ≠ none ∨ targetOf r n = none
    | .loading _ _ _ => False
    | .active _ v => targetOf r n = some v
    | .unloading _ _ _ => False

/-- The withdrawal guard. -/
def relied {N : Type} [DecidableEq N] {K : Type} {V : K → Type u} {E : Type}
    (r : Registry N K V E) (n : N) : Prop :=
  ∃ n' k f, lookup r n' = some f ∧ n' ≠ n ∧ f.lc.installed
    ∧ f.lc.viewOf k = some n

/-- **Faithful state.** The registry together with the ambient remainder. -/
structure State (N : Type) (K : Type) (E : Type) (V : K → Type u) where
  reg : Registry N K V E
  ambient : CoefCtx K V

namespace State

/-- The full context of a faithful state. -/
def fullCtx {N : Type} {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) : Ctx K V :=
  (s.ambient, Faithful.sigmaOf s.reg)

/-- The coeffect context of a faithful state. -/
def sigmaOf {N : Type} {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) : CoefCtx K V :=
  Faithful.sigmaOf s.reg

/-- The provider map of a faithful state. -/
def providerOf {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (k : K) : Option N :=
  Faithful.providerOf s.reg k

/-- The target view of `n` at a faithful state. -/
noncomputable def targetOf {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {E : Type} {V : K → Type u} (s : State N K E V) (n : N) : Option (K → Option N) :=
  Faithful.targetOf s.reg n

/-- Quiescence at a faithful state. -/
def quiet {N : Type} [DecidableEq N] {K : Type} [DecidableEq K] {E : Type}
    {V : K → Type u} (s : State N K E V) : Prop :=
  Faithful.quiet s.reg

/-- The withdrawal guard at a faithful state. -/
def relied {N : Type} [DecidableEq N] {K : Type} {E : Type} {V : K → Type u}
    (s : State N K E V) (n : N) : Prop :=
  Faithful.relied s.reg n

end State

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
      (ht : targetOf s.reg n = some v) :
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
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ.2 }, δ.1⟩
      | none => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ.2 }, δ.1⟩
      | none => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ.2 }, δ.1⟩
      | none => x
  | lUnload n f κ v o hf hl hg, x =>
      match lookup x.reg n with
      | some g => ⟨x.reg, (κ (State.fullCtx x)).1⟩
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
  | lBegin n f v hf hl ht, x =>
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

end Step

end Faithful

end Cordix
