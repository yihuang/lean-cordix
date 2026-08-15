import LeanCordix.FullCalculus

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-
# Cordix — Section 4.4: The trace-indexed model `edit ∘ Ψ`

This module begins the global metatheory of Section 4.4.  It refactors the
table-aware calculus `Full.LstepT`/`Full.Ostep` from a `Prop` relation into a
**Type-level step record** `Step`, so that the acting fiber name and the rule
kind can be extracted computationally.  It also introduces a `State`
structure carrying the registry together with the ambient context, and gives
the state map `Ψ` and the edit `edit` of Definition 53 as ordinary functions
`State → State`.

The factorization `s' = edit (Ψ s)` of Equation (52) is then a theorem
(`Step.factorization`), and the first clauses of Lemma 54 are proved from
the definition of the step record: registry changes are confined to the
acting fiber, and only `L-Unload` moves the ambient context.
-/

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/- State, ambient context, and the rule kind -/

/-- The state of the global calculus: the registry (Definition 45) together
with the ambient remainder of the unified context (the part no fiber table
names).  The coeffect context read by the rules is `Full.sigmaOf s.reg`, the
union of the active tables. -/
structure State (N K E : Type) [DecidableEq N] [DecidableEq K] (V : K → Type u) where
  reg : Registry N K V E
  ambient : CoefCtx K V

namespace State

/-- The coeffect context of a state, read off the active tables. -/
def sigmaOf (s : State N K E V) : CoefCtx K V :=
  Full.sigmaOf s.reg

/-- The provider map of a state. -/
def providerOf (s : State N K E V) (k : K) : Option N :=
  Full.providerOf s.reg k

/-- The target view of `n` at `s`. -/
noncomputable def targetOf (s : State N K E V) (n : N) : Option (K → Option N) :=
  Full.targetOf s.reg n

/-- Quiescence at `s`. -/
def quiet (s : State N K E V) : Prop :=
  Full.quiet s.reg

/-- The withdrawal guard at `s`. -/
def relied (s : State N K E V) (n : N) : Prop :=
  Full.relied s.reg n

end State

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

omit [DecidableEq K] in
/-- Pointwise update is idempotent at the same name. -/
theorem set_set_eq (r : Registry N K V E) (n : N) (f g : Fiber N K V E) :
    set (set r n f) n g = set r n g := by
  induction r with
  | nil => simp [set]
  | cons p rest ih =>
      by_cases h : p.1 = n
      · simp [set, h]
      · simp [set, h, ih]

/- Type-level step records -/

/-- **Definition 53.** A step at a state `s`: the rule kind, the name it
acts on, and all the premises of the rule.  The record is a `Type`, so the
name and kind are data. -/
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
      (ht : Full.targetOf s.reg n = some v) :
      Step s
  | lIter (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (ι' : Iterator (CoefCtx K V) E)
      (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : Full.targetOf s.reg n = some v)
      (hstep : Iterator.step ι (Full.sigmaOf s.reg) = .ok (δ, h, some ι')) :
      Step s
  | lFinish (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : Full.targetOf s.reg n = some v)
      (hstep : Iterator.step ι (Full.sigmaOf s.reg) = .ok (δ, h, none)) :
      Step s
  | lRaise (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (e : E)
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (hstep : Iterator.step ι (Full.sigmaOf s.reg) = .error e) :
      Step s
  | lDivertAbort (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : Full.targetOf s.reg n ≠ some v) :
      Step s
  | lDivertLand (n : N) (f : Fiber N K V E)
      (ι : Iterator (CoefCtx K V) E) (κ : CoefCtx K V → CoefCtx K V)
      (v : K → Option N) (δ : CoefCtx K V) (h : CoefCtx K V → CoefCtx K V)
      (c : Option (Iterator (CoefCtx K V) E))
      (hreach : Iterator.Reachable f.comp.iter ι)
      (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
      (ht : Full.targetOf s.reg n ≠ some v)
      (hstep : Iterator.step ι (Full.sigmaOf s.reg) = .ok (δ, h, c)) :
      Step s
  | lLeave (n : N) (f : Fiber N K V E)
      (κ : CoefCtx K V → CoefCtx K V) (v : K → Option N)
      (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v)
      (ht : Full.targetOf s.reg n ≠ some v) :
      Step s
  | lUnload (n : N) (f : Fiber N K V E)
      (κ : CoefCtx K V → CoefCtx K V) (v : K → Option N) (o : Option E)
      (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o)
      (hg : ¬ Full.relied s.reg n) :
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
def kind : Step s → StepKind
  | oInsert .. => StepKind.oInsert
  | oRetire .. => StepKind.oRetire
  | oRemove .. => StepKind.oRemove
  | lBegin .. => StepKind.lBegin
  | lIter .. => StepKind.lIter
  | lFinish .. => StepKind.lFinish
  | lRaise .. => StepKind.lRaise
  | lDivertAbort .. => StepKind.lDivertAbort
  | lDivertLand .. => StepKind.lDivertLand
  | lLeave .. => StepKind.lLeave
  | lUnload .. => StepKind.lUnload

/-- The state map `Ψ` of Definition 53.  At `L-Iter`, `L-Finish`, and a
landing `L-Divert` it writes the new table produced by the iteration; at
`L-Unload` it applies the fiber's accumulator to the ambient context; at
every other rule it is the identity.  It is defined on every state, using
the fiber currently present in that state. -/
def psi : Step s → State N K E V → State N K E V
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ }, x.ambient⟩
      | none => x
  | lFinish n f ι κ v δ h hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ }, x.ambient⟩
      | none => x
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep, x =>
      match lookup x.reg n with
      | some g => ⟨set x.reg n { g with table := δ }, x.ambient⟩
      | none => x
  | lUnload n f κ v o hf hl hg, x => ⟨x.reg, κ x.ambient⟩
  | _, x => x

/-- The edit `edit` of Definition 53: the bracket read as a total function,
writing only the control fields Table 1 names. -/
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

/-- **Equation (52).** Every step factors as `s' = edit (Ψ s)`. -/
theorem factorization (st : Step s) : next st = edit st (psi st s) := rfl

/-- The registry component of the next state: the ordinary `LstepT`/`Ostep`
relation applied to the registries. -/
theorem regStep (st : Step s) :
    Ostep s.reg (next st).reg ∨ LstepT s.reg (next st).reg := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [next, edit, psi, hn]; exact Or.inl (Ostep.oInsert s.reg n c p hn hp hdisj)
  | oRetire n f hf => simp [next, edit, psi, hf]; exact Or.inl (Ostep.oRetire s.reg n f hf)
  | oRemove n f o hf hl hchild => simp [next, edit, psi, hf, hl]; exact Or.inl (Ostep.oRemove s.reg n f o hf hl hchild)
  | lBegin n f v hf hl ht => simp [next, edit, psi, hf]; exact Or.inr (LstepT.lBegin s.reg n f v hf hl ht)
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep => simp [next, edit, psi, hf, set_set_eq]; exact Or.inr (LstepT.lIter s.reg n f ι κ v ι' δ h hreach hf hl ht hstep)
  | lFinish n f ι κ v δ h hreach hf hl ht hstep => simp [next, edit, psi, hf, set_set_eq]; exact Or.inr (LstepT.lFinish s.reg n f ι κ v δ h hreach hf hl ht hstep)
  | lRaise n f ι κ v e hreach hf hl hstep => simp [next, edit, psi, hf]; exact Or.inr (LstepT.lRaise s.reg n f ι κ v e hreach hf hl hstep)
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [next, edit, psi, hf]; exact Or.inr (LstepT.lDivertAbort s.reg n f ι κ v hreach hf hl ht)
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep => simp [next, edit, psi, hf, set_set_eq]; exact Or.inr (LstepT.lDivertLand s.reg n f ι κ v δ h c hreach hf hl ht hstep)
  | lLeave n f κ v hf hl ht => simp [next, edit, psi, hf]; exact Or.inr (LstepT.lLeave s.reg n f κ v hf hl ht)
  | lUnload n f κ v o hf hl hg => simp [next, edit, psi, hf]; exact Or.inr (LstepT.lUnload s.reg n f κ v o hf hl hg)

/- Lemma 54 -/

/-- **Lemma 54(1), registry form.**  A step changes the registry only at
the fiber it acts on. -/
theorem lookup_next_eq_of_ne (st : Step s) {m : N} (hm : m ≠ st.name) :
    lookup (next st).reg m = lookup s.reg m := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [next, edit, psi, Step.name] at hm ⊢; rw [lookup_set_ne]; exact hm
  | oRetire n f hf => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm
  | oRemove n f o hf hl hchild => simp [next, edit, psi, Step.name] at hm ⊢; rw [lookup_del_ne]; exact hm
  | lBegin n f v hf hl ht => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep => simp [next, edit, psi, Step.name, hf, set_set_eq] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lFinish n f ι κ v δ h hreach hf hl ht hstep => simp [next, edit, psi, Step.name, hf, set_set_eq] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lRaise n f ι κ v e hreach hf hl hstep => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep => simp [next, edit, psi, Step.name, hf, set_set_eq] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lLeave n f κ v hf hl ht => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm
  | lUnload n f κ v o hf hl hg => simp [next, edit, psi, Step.name, hf] at hm ⊢; rw [lookup_set_ne]; exact hm

/-- **Lemma 54(1), fiber form.**  A step changes no field of a fiber it
does not act on. -/
theorem fiber_next_eq_of_ne (st : Step s) {m : N} (hm : m ≠ st.name) :
    ∀ f', lookup (next st).reg m = some f' → lookup s.reg m = some f' := by
  intro f' h
  rw [lookup_next_eq_of_ne st hm] at h
  exact h

/-- **Lemma 54(1), ambient form.**  Only `L-Unload` moves the ambient
context. -/
theorem ambient_next_eq_of_not_lUnload (st : Step s)
    (h : st.kind ≠ StepKind.lUnload) :
    (next st).ambient = s.ambient := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [next, edit, psi, Step.kind]
  | oRetire n f hf => simp [next, edit, psi, Step.kind, hf]
  | oRemove n f o hf hl hchild => simp [next, edit, psi, Step.kind]
  | lBegin n f v hf hl ht => simp [next, edit, psi, Step.kind, hf]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep => simp [next, edit, psi, Step.kind, hf, set_set_eq]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep => simp [next, edit, psi, Step.kind, hf, set_set_eq]
  | lRaise n f ι κ v e hreach hf hl hstep => simp [next, edit, psi, Step.kind, hf]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [next, edit, psi, Step.kind, hf]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep => simp [next, edit, psi, Step.kind, hf, set_set_eq]
  | lLeave n f κ v hf hl ht => simp [next, edit, psi, Step.kind, hf]
  | lUnload n f κ v o hf hl hg => simp [Step.kind] at h
end Step

end Full

end Cordix
