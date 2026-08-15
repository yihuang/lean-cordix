import LeanCordix.FullCalculus

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
(`Step.factorization`).  Lemma 54 is proved from the definition of the step
record: registry changes are confined to the acting fiber, the committed
view is constant through an installed episode, `L-Begin`/`L-Unload` are the
only rules that open/close an episode, `Ψ` writes tables only at the three
iteration rules and the accumulator only at `L-Unload`, and the immutable
fiber fields and monotone retirement flag follow the same case analysis.
The module also defines Type-level `StepTrace`s with preservation of
well-formedness, and proves the deletion lemmas used by Lemma 57: a
vestigial entry contributes nothing to `sigmaOf`, `providerOf`, `targetOf`,
or `relied`, so deleting it leaves those observations unchanged.
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

namespace State

/-- Remove a name from a state. -/
def del (s : State N K E V) (n : N) : State N K E V :=
  ⟨Full.del s.reg n, s.ambient⟩

end State

/-- **Lemma 57.** A name is vestigial at `s` when its entry is retired,
inactive with the trivial outcome, carries an empty table, and no committed
view names it.  The second conjunct records the list-level reading used for
deletion lemmas. -/
def Vestigial (s : State N K E V) (n : N) : Prop :=
  NodupKeys s.reg ∧
    (∀ p ∈ s.reg, p.1 = n → ∃ o, p.2.lc = .inactive o) ∧
    ∃ f : Fiber N K V E,
      lookup s.reg n = some f ∧ f.retired = true ∧ f.lc = .inactive none
        ∧ (∀ k, f.table k = none)
        ∧ ∀ m g, lookup s.reg m = some g → ∀ k, g.lc.viewOf k ≠ some n

/-- `lookup` records membership of the pair it found. -/
theorem lookup_some_mem {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    (h : lookup r n = some f) : (n, f) ∈ r := by
  induction r with
  | nil => simp [lookup] at h
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rw [lookup, if_pos hp] at h
        have hpf : p.2 = f := Option.some.inj h
        subst hpf
        cases p with
        | mk a b =>
            rw [show (n, (a, b).snd) = (a, b) from Prod.ext hp.symm rfl]
            exact List.Mem.head _
      · rw [lookup, if_neg hp] at h
        have hmem := ih h
        simp [hmem]

/-- An inactive head contributes nothing to `sigmaOf`. -/
theorem sigmaOf_cons_inactive (p : N × Fiber N K V E) (rest : Registry N K V E)
    (k : K) (o : Option E) (hlc : p.2.lc = .inactive o) :
    sigmaOf (p :: rest) k = sigmaOf rest k := by
  simp [sigmaOf, List.foldr, hlc]

/-- `sigmaOf` is congruent in the tail of a cons. -/
theorem sigmaOf_cons_congr_k (p : N × Fiber N K V E) {r r' : Registry N K V E}
    (k : K) (hk : sigmaOf r k = sigmaOf r' k) :
    sigmaOf (p :: r) k = sigmaOf (p :: r') k := by
  simp [sigmaOf] at hk ⊢
  cases hlc : p.2.lc <;> simp [hlc, hk]

/-- Deleting entries that are all inactive does not change `sigmaOf`. -/
theorem sigmaOf_del_eq_of_all_inactive (r : Registry N K V E) (n : N)
    (hin : ∀ p ∈ r, p.1 = n → ∃ o, p.2.lc = .inactive o) :
    sigmaOf (del r n) = sigmaOf r := by
  funext k
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rcases hin p (by simp) hp with ⟨o, hlc⟩
        simp [del, hp]
        rw [sigmaOf_cons_inactive p rest k o hlc]
        exact ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn)
      · simp [del, hp]
        exact sigmaOf_cons_congr_k p k (ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn))

/-- An inactive head contributes nothing to `providerOf`. -/
theorem providerOf_cons_inactive (p : N × Fiber N K V E) (rest : Registry N K V E)
    (k : K) (o : Option E) (hlc : p.2.lc = .inactive o) :
    providerOf (p :: rest) k = providerOf rest k := by
  simp [providerOf, List.foldr, hlc]

/-- `providerOf` is congruent in the tail of a cons. -/
theorem providerOf_cons_congr_k (p : N × Fiber N K V E) {r r' : Registry N K V E}
    (k : K) (hk : providerOf r k = providerOf r' k) :
    providerOf (p :: r) k = providerOf (p :: r') k := by
  simp [providerOf] at hk ⊢
  cases hlc : p.2.lc <;> simp [hlc, hk]

/-- Deleting entries that are all inactive does not change `providerOf`. -/
theorem providerOf_del_eq_of_all_inactive (r : Registry N K V E) (n : N)
    (hin : ∀ p ∈ r, p.1 = n → ∃ o, p.2.lc = .inactive o) :
    providerOf (del r n) = providerOf r := by
  funext k
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rcases hin p (by simp) hp with ⟨o, hlc⟩
        simp [del, hp]
        rw [providerOf_cons_inactive p rest k o hlc]
        exact ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn)
      · simp [del, hp]
        exact providerOf_cons_congr_k p k (ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn))

/-- Deleting a vestigial entry does not change `sigmaOf`. -/
theorem sigmaOf_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : sigmaOf (del s.reg n) = sigmaOf s.reg :=
  sigmaOf_del_eq_of_all_inactive s.reg n h.2.1

/-- Deleting a vestigial entry does not change `providerOf`. -/
theorem providerOf_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : providerOf (del s.reg n) = providerOf s.reg :=
  providerOf_del_eq_of_all_inactive s.reg n h.2.1

/-- Deleting a vestigial entry does not change the target view of any other
name. -/
theorem targetOf_del_eq_of_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n) :
    targetOf (del s.reg n) m = targetOf s.reg m := by
  unfold targetOf
  rw [lookup_del_ne s.reg n m hm]
  have hsig := sigmaOf_del_eq_of_vestigial h
  have hprov := providerOf_del_eq_of_vestigial h
  simp [hsig, hprov]

/-- Deleting a vestigial entry does not change the withdrawal guard of any
other name. -/
theorem relied_del_eq_of_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n) :
    relied (del s.reg n) m ↔ relied s.reg m := by
  unfold relied
  constructor
  · rintro ⟨n', k, f, hlook, hne, hinst, hv⟩
    have hc := lookup_del_cases (n := n) hlook
    exact ⟨n', k, f, hc.2, hne, hinst, hv⟩
  · rintro ⟨n', k, f, hlook, hne, hinst, hv⟩
    have hn' : n' ≠ n := by
      intro hEq; subst n'
      have hmem := lookup_some_mem hlook
      rcases h.2.1 (n, f) hmem rfl with ⟨o, hlc⟩
      rw [hlc] at hinst
      cases hinst
    have hlookD : lookup (del s.reg n) n' = some f := by
      rw [lookup_del_ne]
      exact hlook
      exact hn'
    exact ⟨n', k, f, hlookD, hne, hinst, hv⟩

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

/-- The only observation through which a step can mention a name other
than the one it acts on: the parent premise of `O-Insert`.  This predicate
records that the parent does not mention `n`. -/
def avoidsInsertParent : Step s → N → Prop
  | oInsert n c p hn hp hdisj, m => m ∉ p
  | _, _ => True

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

/-! ## Lemma 57, first half: deleting a vestigial entry -/

/-- **Lemma 57(1), applicability half.**  If `n` is vestigial at `s`, then
any step acting on another name remains applicable after `n` is deleted;
for `O-Insert` the usual extra parent/fresh-name caveat is expressed by
`avoidsInsertParent`.  The transported step has the same name and rule. -/
theorem step_del_of_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n)
    (st : Step s) (hname : st.name = m) (havoid : Step.avoidsInsertParent st n) :
    ∃ st' : Step (State.del s n), st'.name = m ∧ st'.kind = st.kind := by
  cases st with
  | oInsert a c p hn hp hdisj =>
      subst m
      have ha : a ≠ n := by
        intro hEq; subst a; exact hm rfl
      have hlookD : lookup (State.del s n).reg a = none := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hn
        exact ha
      have hpD : ∀ n' ∈ p, ∃ f, lookup (State.del s n).reg n' = some f := by
        intro n' hn'p
        rcases hp n' hn'p with ⟨f, hf⟩
        have hn' : n' ≠ n := by
          intro hEq; subst n'
          exact havoid hn'p
        refine ⟨f, ?_⟩
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact hn'
      have hdisjD : ∀ n' f, lookup (State.del s n).reg n' = some f →
          (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k') := by
        intro n' f hlook
        by_cases hn' : n' = n
        · subst n'
          simp [State.del] at hlook
        · have hlookR : lookup s.reg n' = some f := by
            simpa [State.del] using (lookup_del_cases (n := n) hlook).2
          exact hdisj n' f hlookR
      exact ⟨Step.oInsert (s := State.del s n) a c p hlookD hpD hdisjD, rfl, rfl⟩
  | oRetire a f hf =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      exact ⟨Step.oRetire (s := State.del s n) a f hfD, rfl, rfl⟩
  | oRemove a f o hf hl hchild =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have hchildD : ∀ n' f', lookup (State.del s n).reg n' = some f' → f'.parent ≠ some a := by
        intro n' f' hlook
        by_cases hn' : n' = n
        · subst n'; simp [State.del] at hlook
        · have hlookR : lookup s.reg n' = some f' := by
            simpa [State.del] using (lookup_del_cases (n := n) hlook).2
          exact hchild n' f' hlookR
      exact ⟨Step.oRemove (s := State.del s n) a f o hfD hl hchildD, rfl, rfl⟩
  | lBegin a f v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : targetOf (State.del s n).reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      exact ⟨Step.lBegin (s := State.del s n) a f v hfD hl htD, rfl, rfl⟩
  | lIter a f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : targetOf (State.del s n).reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      have hstepD : Cordix.Iterator.step ι (sigmaOf (State.del s n).reg) = Except.ok (δ, hinv, some ι') := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lIter (s := State.del s n) a f ι κ v ι' δ hinv hreach hfD hl htD hstepD, rfl, rfl⟩
  | lFinish a f ι κ v δ hinv hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have htD : targetOf (State.del s n).reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      have hstepD : Cordix.Iterator.step ι (sigmaOf (State.del s n).reg) = Except.ok (δ, hinv, none) := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lFinish (s := State.del s n) a f ι κ v δ hinv hreach hfD hl htD hstepD, rfl, rfl⟩
  | lRaise a f ι κ v e hreach hf hl hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have hstepD : Cordix.Iterator.step ι (sigmaOf (State.del s n).reg) = Except.error e := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lRaise (s := State.del s n) a f ι κ v e hreach hfD hl hstepD, rfl, rfl⟩
  | lDivertAbort a f ι κ v hreach hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have htD : targetOf (State.del s n).reg a ≠ some v := by
        intro hbad
        have ht' : targetOf s.reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht ht'
      exact ⟨Step.lDivertAbort (s := State.del s n) a f ι κ v hreach hfD hl htD, rfl, rfl⟩
  | lDivertLand a f ι κ v δ hinv c hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have htD : targetOf (State.del s n).reg a ≠ some v := by
        intro hbad
        have ht' : targetOf s.reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht ht'
      have hstepD : Cordix.Iterator.step ι (sigmaOf (State.del s n).reg) = Except.ok (δ, hinv, c) := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lDivertLand (s := State.del s n) a f ι κ v δ hinv c hreach hfD hl htD hstepD, rfl, rfl⟩
  | lLeave a f κ v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have htD : targetOf (State.del s n).reg a ≠ some v := by
        intro hbad
        have ht' : targetOf s.reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht ht'
      exact ⟨Step.lLeave (s := State.del s n) a f κ v hfD hl htD, rfl, rfl⟩
  | lUnload a f κ v o hf hl hg =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]; rw [lookup_del_ne]; exact hf; exact ha
      have hgD : ¬ relied (State.del s n).reg a := by
        intro hbad
        have hg' : relied s.reg a := (relied_del_eq_of_vestigial h ha).mp (by simpa [State.del] using hbad)
        exact hg hg'
      exact ⟨Step.lUnload (s := State.del s n) a f κ v o hfD hl hgD, rfl, rfl⟩

/-- The ways a step at `s.del n` cannot be lifted back to `s`: an
`O-Insert` drawing the vestigial name or claiming a key of its provision,
or an `O-Remove` whose no-child premise would have to inspect the deleted
vestigial entry. -/
def InsertConflict (s : State N K E V) (n : N) : Step (State.del s n) → Prop
  | Step.oInsert a c p hn hp hdisj =>
      a = n ∨ ∃ f : Fiber N K V E, lookup s.reg n = some f
          ∧ ∃ k : K, k ∈ c.prov ∧ k ∈ f.comp.prov
  | Step.oRemove a f o hf hl hchild =>
      ∃ fv : Fiber N K V E, lookup s.reg n = some fv ∧ fv.parent = some a
  | _ => False

/-- **Lemma 57(2), lifting half.**  A step at `s.del n` acting on another
name lifts back to `s`, except for the `O-Insert`/`O-Remove` conflicts
recorded by `InsertConflict`. -/
theorem step_of_del_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n)
    (st : Step (State.del s n)) (hname : st.name = m)
    (hno : ¬ InsertConflict s n st) :
    ∃ st' : Step s, st'.name = m ∧ st'.kind = st.kind := by
  cases st with
  | oInsert a c p hn hp hdisj =>
      subst m
      have ha : a ≠ n := by
        intro hEq
        exact hno (Or.inl hEq)
      have hlookR : lookup s.reg a = none := by
        have hd := lookup_del_ne s.reg n a ha
        simp [State.del] at hn
        rw [hd] at hn
        exact hn
      have hpR : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f := by
        intro n' hn'p
        rcases hp n' hn'p with ⟨f, hf⟩
        have hn' : n' ≠ n := by
          intro hEq; subst n'
          simp [State.del] at hf
        refine ⟨f, ?_⟩
        exact (lookup_del_cases (n := n) hf).2
      have hdisjR : ∀ n' f, lookup s.reg n' = some f →
          (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k') := by
        intro n' f hlook k hk k' hk'
        by_cases hn' : n' = n
        · subst n'
          intro hEq
          exact hno (Or.inr ⟨f, hlook, ⟨k, hk, by simpa [hEq] using hk'⟩⟩)
        · have hlookD : lookup (State.del s n).reg n' = some f := by
            simp [State.del]
            rw [lookup_del_ne]
            exact hlook
            exact hn'
          exact hdisj n' f hlookD k hk k' hk'
      exact ⟨Step.oInsert (s := s) a c p hlookR hpR hdisjR, rfl, rfl⟩
  | oRetire a f hf =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by
        exact (lookup_del_cases (n := n) hf).2
      exact ⟨Step.oRetire (s := s) a f hfR, rfl, rfl⟩
  | oRemove a f o hf hl hchild =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by
        exact (lookup_del_cases (n := n) hf).2
      simp [InsertConflict] at hno
      have hchildR : ∀ n' f', lookup s.reg n' = some f' → f'.parent ≠ some a := by
        intro n' f' hlook
        by_cases hn' : n' = n
        · subst n'
          intro hparent
          exact hno f' hlook hparent
        · have hlookD : lookup (State.del s n).reg n' = some f' := by
            simp [State.del]; rw [lookup_del_ne]; exact hlook; exact hn'
          exact hchild n' f' hlookD
      exact ⟨Step.oRemove (s := s) a f o hfR hl hchildR, rfl, rfl⟩
  | lBegin a f v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by
        exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      exact ⟨Step.lBegin (s := s) a f v hfR hl htR, rfl, rfl⟩
  | lIter a f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      have hstepR : Cordix.Iterator.step ι (sigmaOf s.reg) = Except.ok (δ, hinv, some ι') := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lIter (s := s) a f ι κ v ι' δ hinv hreach hfR hl htR hstepR, rfl, rfl⟩
  | lFinish a f ι κ v δ hinv hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a = some v := by
        simpa [State.del, targetOf_del_eq_of_vestigial h ha] using ht
      have hstepR : Cordix.Iterator.step ι (sigmaOf s.reg) = Except.ok (δ, hinv, none) := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lFinish (s := s) a f ι κ v δ hinv hreach hfR hl htR hstepR, rfl, rfl⟩
  | lRaise a f ι κ v e hreach hf hl hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have hstepR : Cordix.Iterator.step ι (sigmaOf s.reg) = Except.error e := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lRaise (s := s) a f ι κ v e hreach hfR hl hstepR, rfl, rfl⟩
  | lDivertAbort a f ι κ v hreach hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a ≠ some v := by
        intro hbad
        have hbadD : targetOf (State.del s n).reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht hbadD
      exact ⟨Step.lDivertAbort (s := s) a f ι κ v hreach hfR hl htR, rfl, rfl⟩
  | lDivertLand a f ι κ v δ hinv c hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a ≠ some v := by
        intro hbad
        have hbadD : targetOf (State.del s n).reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht hbadD
      have hstepR : Cordix.Iterator.step ι (sigmaOf s.reg) = Except.ok (δ, hinv, c) := by
        simpa [State.del, sigmaOf_del_eq_of_vestigial h] using hstep
      exact ⟨Step.lDivertLand (s := s) a f ι κ v δ hinv c hreach hfR hl htR hstepR, rfl, rfl⟩
  | lLeave a f κ v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : targetOf s.reg a ≠ some v := by
        intro hbad
        have hbadD : targetOf (State.del s n).reg a = some v := by
          simpa [State.del, targetOf_del_eq_of_vestigial h ha] using hbad
        exact ht hbadD
      exact ⟨Step.lLeave (s := s) a f κ v hfR hl htR, rfl, rfl⟩
  | lUnload a f κ v o hf hl hg =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have hgR : ¬ relied s.reg a := by
        intro hbad
        have hbadD : relied (State.del s n).reg a := by
          exact (relied_del_eq_of_vestigial h ha).mpr (by simpa [State.del] using hbad)
        exact hg hbadD
      exact ⟨Step.lUnload (s := s) a f κ v o hfR hl hgR, rfl, rfl⟩

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
/-- A step whose `Ψ` writes no table leaves the acting fiber's table
unchanged. -/
theorem table_next_eq_of_not_writesTable (st : Step s)
    (h : ¬ StepKind.writesTable st.kind) {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (next st).reg st.name = some f') :
    f'.table = f.table := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [next, edit, psi, Step.name] at hf hf'; rw [hn] at hf; cases hf
  | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl
  | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name] at hf hf'
  | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl
  | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [Step.kind, StepKind.writesTable] at h
  | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [Step.kind, StepKind.writesTable] at h
  | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl
  | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl
  | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [Step.kind, StepKind.writesTable] at h
  | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl
  | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0] at hf hf'; cases hf; cases hf'; rfl

/-- **Lemma 54(2).** The committed view changes only at `L-Begin` and
`L-Unload`; in particular it is constant while both old and new lifecycle
states are installed. -/
theorem viewOf_next_eq_of_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (next st).reg st.name = some f')
    (hinst : f.lc.installed) (hinst' : f'.lc.installed) :
    f'.lc.viewOf = f.lc.viewOf := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [next, edit, psi, Step.name, hn] at hf hf'
  | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; rfl
  | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name, hf0] at hf hf'
  | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl]; cases hf'; rfl
  | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; cases hinst'

/-- **Lemma 54(4), opening.**  An installed fiber can only come into
existence at `L-Begin` of that fiber. -/
theorem installed_next_of_not_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (next st).reg st.name = some f')
    (hinst : ¬ f.lc.installed) (hinst' : f'.lc.installed) :
    st.kind = StepKind.lBegin := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.name, hn] at hf
  | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; exact False.elim (hinst hinst')
  | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name, hf0] at hf'
  | lBegin n f v hf0 hl ht => rfl
  | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; cases hinst'

/-- **Lemma 54(4), closing.**  An installed fiber can only cease to be
installed at `L-Unload` of that fiber. -/
theorem not_installed_next_of_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (next st).reg st.name = some f')
    (hinst : f.lc.installed) (hinst' : ¬ f'.lc.installed) :
    st.kind = StepKind.lUnload := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.name, hn] at hf
  | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; change ¬ f.lc.installed at hinst'; exact False.elim (hinst' hinst)
  | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name, hf0] at hf'
  | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; rw [hl] at hinst; simp [Lifecycle.installed] at hinst
  | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0, hl] at hf hf' ⊢; cases hf; cases hf'; simp [Lifecycle.installed] at hinst'
  | lUnload n f κ v o hf0 hl hg => rfl

/-- **Lemma 54(5).** The component and parent fields are written once,
when the fiber is inserted; they never change afterward. -/
theorem comp_parent_next_eq (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (next st).reg m = some f') :
    f'.comp = f.comp ∧ f'.parent = f.parent := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj => simp [Step.name, hn] at hf
    | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name] at hf'
    | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
    | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    cases hff
    simp

/-- **Lemma 54(5), retired monotonicity.**  The retirement flag only
changes from `false` to `true`, and only by `O-Retire` acting on that
fiber. -/
theorem retired_monotone (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (next st).reg m = some f')
    (hret : f.retired = true) : f'.retired = true := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj => simp [Step.name, hn] at hf
    | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; rfl
    | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name] at hf'
    | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
    | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0] at hf hf' ⊢; cases hf; cases hf'; simp [hret]
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    rw [← hff]
    exact hret

/-- **Lemma 54(5), retired only by `O-Retire`.**  A retirement flag that
is newly true can only be written by `O-Retire` acting on that fiber. -/
theorem retired_changed_iff (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (next st).reg m = some f')
    (hnot : f.retired = false) (hret : f'.retired = true) :
    st.name = m ∧ st.kind = StepKind.oRetire := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj => simp [Step.name, hn] at hf
    | oRetire n f hf0 => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; rfl
    | oRemove n f o hf0 hl hchild => simp [next, edit, psi, Step.name] at hf'
    | lBegin n f v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lRaise n f ι κ v e hreach hf0 hl hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lLeave n f κ v hf0 hl ht => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
    | lUnload n f κ v o hf0 hl hg => simp [next, edit, psi, Step.name, hf0] at hf hf' hnot hret ⊢; cases hf; cases hf'; rw [hnot] at hret; cases hret
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    rw [← hff] at hret
    rw [hnot] at hret
    cases hret

/-- **Lemma 54(3), ambient half.**  Only `L-Unload` applies the
accumulator to the ambient context; every other `Ψ` leaves the ambient
context alone. -/
theorem psi_ambient_eq_of_not_lUnload (st : Step s)
    (h : st.kind ≠ StepKind.lUnload) :
    ∀ x, (psi st x).ambient = x.ambient := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [psi, Step.kind]
  | oRetire n f hf0 => simp [psi, Step.kind]
  | oRemove n f o hf0 hl hchild => simp [psi, Step.kind]
  | lBegin n f v hf0 hl ht => simp [psi, Step.kind]
  | lIter n f ι κ v ι' δ hinv hreach hf0 hl ht hstep =>
      simp [psi, Step.kind]
      intro x
      cases hx : lookup x.reg n <;> simp [hx]
  | lFinish n f ι κ v δ hinv hreach hf0 hl ht hstep =>
      simp [psi, Step.kind]
      intro x
      cases hx : lookup x.reg n <;> simp [hx]
  | lRaise n f ι κ v e hreach hf0 hl hstep => simp [psi, Step.kind]
  | lDivertAbort n f ι κ v hreach hf0 hl ht => simp [psi, Step.kind]
  | lDivertLand n f ι κ v δ hinv c hreach hf0 hl ht hstep =>
      simp [psi, Step.kind]
      intro x
      cases hx : lookup x.reg n <;> simp [hx]
  | lLeave n f κ v hf0 hl ht => simp [psi, Step.kind]
  | lUnload n f κ v o hf0 hl hg => simp [Step.kind] at h

/-- **Lemma 54(3), table half.**  A `Ψ` that writes no table leaves every
registry unchanged. -/
theorem psi_reg_eq_of_not_writesTable (st : Step s)
    (h : ¬ StepKind.writesTable st.kind) :
    ∀ x, (psi st x).reg = x.reg := by
  cases st <;> simp [psi, Step.kind, StepKind.writesTable] at h ⊢



/-! ## Type-level traces -/

/-- A finite trace of `Step` records.  The `hnext` field ties each record
to the state the following trace starts at. -/
inductive StepTrace : State N K E V → State N K E V → Type (max 1 u) where
  | nil (s : State N K E V) : StepTrace s s
  | cons {s₁ s₂ s₃ : State N K E V} (st : Step s₁) (hnext : next st = s₂)
      (ht : StepTrace s₂ s₃) : StepTrace s₁ s₃

namespace StepTrace

/-- **Theorem 59 along Type-level traces.**  Well-formedness is preserved
by every finite `Step` trace. -/
theorem wellFormed_preserved {s s' : State N K E V}
    (h : WellFormed s.reg) (ht : StepTrace s s') : WellFormed s'.reg := by
  induction ht with
  | nil s => exact h
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      exact ih (by
        rw [← hnext]
        exact WellFormed.preservedT h (Step.regStep st))

end StepTrace

end Step

end Full

end Cordix
