import LeanCordix.FullCtx
import LeanCordix.Iterator
import LeanCordix.Coeffect

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

end Faithful

end Cordix
