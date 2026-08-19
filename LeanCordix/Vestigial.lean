import LeanCordix.Basic
import LeanCordix.Step
import LeanCordix.Trace
import LeanCordix.WellFormed

/-!
# LeanCordix.Vestigial — Lemma 54/57: vestigial entries and step locality

This module ports the deleted legacy metatheory for vestigial entries and the
step-local preservation lemmas from `/tmp/oldrepo/TraceModel.lean` onto the
current faithful full-context model.

In the current model the step map `Ψ` is a `State → State` map that writes
full-context effects (`State.writeEffect`) at iterator rules and at
`L-Unload`.  The statements below are therefore adapted where the old
`CoefCtx`-only model had simpler ambient/table preservation lemmas.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

namespace State

/-- Delete a name from a faithful state, keeping the ambient context. -/
def del (s : State N K E V) (n : N) : State N K E V :=
  ⟨Cordix.del s.reg n, s.ambient⟩

end State

/-- **Lemma 57.** A name is vestigial at `s` when its entry is retired,
inactive with the trivial outcome, carries an empty table, and no committed
view names it.  The first two conjuncts record the list-level reading used
for deletion lemmas. -/
def Vestigial (s : State N K E V) (n : N) : Prop :=
  NodupKeys s.reg ∧
    (∀ p ∈ s.reg, p.1 = n → ∃ o, p.2.lc = .inactive o) ∧
    ∃ f : Fiber N K V E,
      lookup s.reg n = some f ∧ f.retired = true ∧ f.lc = .inactive none
        ∧ (∀ k, f.table k = none)
        ∧ ∀ m g, lookup s.reg m = some g → ∀ k, g.lc.viewOf k ≠ some n

/-- `lookup` records membership of the pair it found. -/
theorem lookup_some_mem_vestigial {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    (h : lookup r n = some f) : (n, f) ∈ r := by
  induction r with
  | nil => cases h
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rw [lookup, if_pos hp] at h
        have hpf : p.2 = f := Option.some.inj h
        cases p with
        | mk n' g =>
            simp at hp hpf ⊢
            subst n'
            subst f
            simp
      · rw [lookup, if_neg hp] at h
        exact List.mem_cons_of_mem p (ih h)

/-- Every occurrence of a vestigial name has the empty table. -/
theorem table_none_of_vestigial_mem {s : State N K E V} {n : N}
    (h : Vestigial s n) {p : N × Fiber N K V E} (hp : p ∈ s.reg)
    (hpn : p.1 = n) : p.2.table = fun _ => none := by
  rcases h.2.2 with ⟨f, hf, hret, hl, htable, hviews⟩
  rcases p with ⟨a, g⟩
  have ha : a = n := by simpa using hpn
  subst a
  have hlook_g : lookup s.reg n = some g := by
    simpa using (lookup_self_of_mem_of_nodup h.1 hp)
  have hlook_f : lookup s.reg n = some f := hf
  have hg : g = f := lookup_eq_of_nodup h.1 hlook_g hlook_f
  subst g
  funext k
  exact htable k

/-- An inactive head contributes nothing to `sigmaOf`. -/
theorem sigmaOf_cons_inactive (p : N × Fiber N K V E) (rest : Registry N K V E)
    (k : K) (o : Option E) (hlc : p.2.lc = .inactive o) :
    Cordix.sigmaOf (p :: rest) k = Cordix.sigmaOf rest k := by
  simp [Cordix.sigmaOf, hlc]

/-- `sigmaOf` is congruent in the tail of a cons. -/
theorem sigmaOf_cons_congr_k (p : N × Fiber N K V E) {r r' : Registry N K V E}
    (k : K) (hk : Cordix.sigmaOf r k = Cordix.sigmaOf r' k) :
    Cordix.sigmaOf (p :: r) k = Cordix.sigmaOf (p :: r') k := by
  simp [Cordix.sigmaOf] at hk ⊢
  cases hlc : p.2.lc <;> simp [hlc, hk]

/-- Deleting entries that are all inactive does not change `sigmaOf`. -/
theorem sigmaOf_del_eq_of_all_inactive (r : Registry N K V E) (n : N)
    (hin : ∀ p ∈ r, p.1 = n → ∃ o, p.2.lc = .inactive o) :
    Cordix.sigmaOf (del r n) = Cordix.sigmaOf r := by
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
    Cordix.providerOf (p :: rest) k = Cordix.providerOf rest k := by
  simp [Cordix.providerOf, hlc]

/-- `providerOf` is congruent in the tail of a cons. -/
theorem providerOf_cons_congr_k (p : N × Fiber N K V E) {r r' : Registry N K V E}
    (k : K) (hk : Cordix.providerOf r k = Cordix.providerOf r' k) :
    Cordix.providerOf (p :: r) k = Cordix.providerOf (p :: r') k := by
  simp [Cordix.providerOf] at hk ⊢
  cases hlc : p.2.lc <;> simp [hlc, hk]

/-- Deleting entries that are all inactive does not change `providerOf`. -/
theorem providerOf_del_eq_of_all_inactive (r : Registry N K V E) (n : N)
    (hin : ∀ p ∈ r, p.1 = n → ∃ o, p.2.lc = .inactive o) :
    Cordix.providerOf (del r n) = Cordix.providerOf r := by
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

/-- Deleting a vestigial entry does not change the raw sigma (all tables). -/
theorem rawSigma_del_eq_of_all_empty_inactive (r : Registry N K V E) (n : N)
    (hin : ∀ p ∈ r, p.1 = n → (∃ o, p.2.lc = .inactive o) ∧ p.2.table = fun _ => none) :
    rawSigma (del r n) = rawSigma r := by
  funext k
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · rcases (hin p (by simp) hp) with ⟨⟨o, hlc⟩, htable⟩
        have hnone : p.2.table k = none := congrFun htable k
        simp [del, hp, rawSigma, hnone]
        simpa [rawSigma] using
          ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn)
      · simp [del, hp, rawSigma]
        have htail : rawSigma (del rest n) k = rawSigma rest k :=
          ih (by intro q hq hqn; exact hin q (by simp [hq]) hqn)
        have htail' : List.foldr (fun p acc => (p.snd.table k).or acc) none (del rest n) =
            List.foldr (fun p acc => (p.snd.table k).or acc) none rest := by
          simpa [rawSigma] using htail
        rw [htail']

/-- Deleting a vestigial entry does not change the raw sigma (all tables). -/
theorem rawSigma_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : rawSigma (del s.reg n) = rawSigma s.reg := by
  apply rawSigma_del_eq_of_all_empty_inactive s.reg n
  intro p hp hpn
  constructor
  · exact h.2.1 p hp hpn
  · exact table_none_of_vestigial_mem h hp hpn

/-- Deleting a vestigial entry does not change the faithful full context. -/
theorem fullCtx_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : State.fullCtx (State.del s n) = State.fullCtx s := by
  simp [State.del, State.fullCtx, rawSigma_del_eq_of_vestigial h]

/-- Deleting a vestigial entry does not change `sigmaOf`. -/
theorem sigmaOf_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : Cordix.sigmaOf (del s.reg n) = Cordix.sigmaOf s.reg :=
  sigmaOf_del_eq_of_all_inactive s.reg n h.2.1

/-- Deleting a vestigial entry does not change `providerOf`. -/
theorem providerOf_del_eq_of_vestigial {s : State N K E V} {n : N}
    (h : Vestigial s n) : Cordix.providerOf (del s.reg n) = Cordix.providerOf s.reg :=
  providerOf_del_eq_of_all_inactive s.reg n h.2.1

/-- Deleting a vestigial entry does not change the target view of any other
name. -/
theorem targetOf_del_eq_of_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n) :
    State.targetOf (State.del s n) m = State.targetOf s m := by
  unfold State.targetOf Cordix.targetOf State.del
  rw [lookup_del_ne (r := s.reg) (n := n) (m := m) hm]
  have hsig := sigmaOf_del_eq_of_vestigial h
  have hprov := providerOf_del_eq_of_vestigial h
  simp [hsig, hprov]

/-- Deleting a vestigial entry does not change the withdrawal guard of any
other name. -/
theorem relied_del_eq_of_vestigial {s : State N K E V} {n m : N}
    (h : Vestigial s n) (hm : m ≠ n) :
    State.relied (State.del s n) m ↔ State.relied s m := by
  unfold State.relied State.del
  constructor
  · rintro ⟨n', k, f, hlook, hne, hinst, hv⟩
    have hc := lookup_del_cases (n := n) hlook
    exact ⟨n', k, f, hc.2, hne, hinst, hv⟩
  · rintro ⟨n', k, f, hlook, hne, hinst, hv⟩
    have hn' : n' ≠ n := by
      intro hEq; subst n'
      have hmem := lookup_some_mem_vestigial hlook
      rcases h.2.1 (n, f) hmem rfl with ⟨o, hlc⟩
      rw [hlc] at hinst
      cases hinst
    have hlookD : lookup (del s.reg n) n' = some f := by
      rw [lookup_del_ne (r := s.reg) (n := n) (m := n') hn']
      exact hlook
    exact ⟨n', k, f, hlookD, hne, hinst, hv⟩

namespace Step

variable {s : State N K E V}

/-- The only observation through which a step can mention a name other
than the one it acts on: the parent premise of `O-Insert`.  This predicate
records that the parent does not mention `n`. -/
def avoidsInsertParent : Step s → N → Prop
  | oInsert n c p hn hp hdisj, m => m ∉ p
  | _, _ => True

end Step

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

/-- **Lemma 57(1), applicability half.**  If `n` is vestigial at `s`, then
any step acting on another name remains applicable after `n` is deleted;
for `O-Insert` the usual extra parent/fresh-name caveat is expressed by
`Step.avoidsInsertParent`.  The transported step has the same name and rule. -/
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
          simp [State.del, lookup_del_self] at hlook
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
        · subst n'; simp [State.del, lookup_del_self] at hlook
        · have hlookR : lookup s.reg n' = some f' := by
            simpa [State.del] using (lookup_del_cases (n := n) hlook).2
          exact hchild n' f' hlookR
      exact ⟨Step.oRemove (s := State.del s n) a f o hfD hl hchildD, rfl, rfl⟩
  | lBegin a f v hf hl ht htable =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a = some v := by
        rw [targetOf_del_eq_of_vestigial h ha]
        exact ht
      exact ⟨Step.lBegin (s := State.del s n) a f v hfD hl htD htable, rfl, rfl⟩
  | lIter a f ι κ v ι' δ h' hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a = some v := by
        rw [targetOf_del_eq_of_vestigial h ha]
        exact ht
      have hstepD : Iterator.step ι (State.fullCtx (State.del s n)) = .ok (δ, h', some ι') := by
        rw [fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lIter (s := State.del s n) a f ι κ v ι' δ h' hreach hfD hl htD hstepD, rfl, rfl⟩
  | lFinish a f ι κ v δ h' hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a = some v := by
        rw [targetOf_del_eq_of_vestigial h ha]
        exact ht
      have hstepD : Iterator.step ι (State.fullCtx (State.del s n)) = .ok (δ, h', none) := by
        rw [fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lFinish (s := State.del s n) a f ι κ v δ h' hreach hfD hl htD hstepD, rfl, rfl⟩
  | lRaise a f ι κ v e hreach hf hl hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have hstepD : Iterator.step ι (State.fullCtx (State.del s n)) = .error e := by
        rw [fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lRaise (s := State.del s n) a f ι κ v e hreach hfD hl hstepD, rfl, rfl⟩
  | lDivertAbort a f ι κ v hreach hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a ≠ some v := by
        intro hbad
        have ht' : State.targetOf s a = some v := by
          rw [← targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht ht'
      exact ⟨Step.lDivertAbort (s := State.del s n) a f ι κ v hreach hfD hl htD, rfl, rfl⟩
  | lDivertLand a f ι κ v δ h' c hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a ≠ some v := by
        intro hbad
        have ht' : State.targetOf s a = some v := by
          rw [← targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht ht'
      have hstepD : Iterator.step ι (State.fullCtx (State.del s n)) = .ok (δ, h', c) := by
        rw [fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lDivertLand (s := State.del s n) a f ι κ v δ h' c hreach hfD hl htD hstepD, rfl, rfl⟩
  | lLeave a f κ v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have htD : State.targetOf (State.del s n) a ≠ some v := by
        intro hbad
        have ht' : State.targetOf s a = some v := by
          rw [← targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht ht'
      exact ⟨Step.lLeave (s := State.del s n) a f κ v hfD hl htD, rfl, rfl⟩
  | lUnload a f κ v o hf hl hg =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfD : lookup (State.del s n).reg a = some f := by
        simp [State.del]
        rw [lookup_del_ne]
        exact hf
        exact ha
      have hgD : ¬ State.relied (State.del s n) a := by
        intro hbad
        have hg' : State.relied s a := (relied_del_eq_of_vestigial h ha).mp (by simpa [State.del] using hbad)
        exact hg hg'
      exact ⟨Step.lUnload (s := State.del s n) a f κ v o hfD hl hgD, rfl, rfl⟩

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
        have hd := lookup_del_ne (r := s.reg) (n := n) (m := a) ha
        simp [State.del] at hn
        rw [hd] at hn
        exact hn
      have hpR : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f := by
        intro n' hn'p
        rcases hp n' hn'p with ⟨f, hf⟩
        have hn' : n' ≠ n := by
          intro hEq; subst n'
          simp [State.del, lookup_del_self] at hf
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
            simp [State.del]
            rw [lookup_del_ne]
            exact hlook
            exact hn'
          exact hchild n' f' hlookD
      exact ⟨Step.oRemove (s := s) a f o hfR hl hchildR, rfl, rfl⟩
  | lBegin a f v hf hl ht htable =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by
        exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a = some v := by
        rw [← targetOf_del_eq_of_vestigial h ha]
        exact ht
      exact ⟨Step.lBegin (s := s) a f v hfR hl htR htable, rfl, rfl⟩
  | lIter a f ι κ v ι' δ h' hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a = some v := by
        rw [← targetOf_del_eq_of_vestigial h ha]
        exact ht
      have hstepR : Iterator.step ι (State.fullCtx s) = .ok (δ, h', some ι') := by
        rw [← fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lIter (s := s) a f ι κ v ι' δ h' hreach hfR hl htR hstepR, rfl, rfl⟩
  | lFinish a f ι κ v δ h' hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a = some v := by
        rw [← targetOf_del_eq_of_vestigial h ha]
        exact ht
      have hstepR : Iterator.step ι (State.fullCtx s) = .ok (δ, h', none) := by
        rw [← fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lFinish (s := s) a f ι κ v δ h' hreach hfR hl htR hstepR, rfl, rfl⟩
  | lRaise a f ι κ v e hreach hf hl hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have hstepR : Iterator.step ι (State.fullCtx s) = .error e := by
        rw [← fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lRaise (s := s) a f ι κ v e hreach hfR hl hstepR, rfl, rfl⟩
  | lDivertAbort a f ι κ v hreach hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a ≠ some v := by
        intro hbad
        have hbadD : State.targetOf (State.del s n) a = some v := by
          rw [targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht hbadD
      exact ⟨Step.lDivertAbort (s := s) a f ι κ v hreach hfR hl htR, rfl, rfl⟩
  | lDivertLand a f ι κ v δ h' c hreach hf hl ht hstep =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a ≠ some v := by
        intro hbad
        have hbadD : State.targetOf (State.del s n) a = some v := by
          rw [targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht hbadD
      have hstepR : Iterator.step ι (State.fullCtx s) = .ok (δ, h', c) := by
        rw [← fullCtx_del_eq_of_vestigial h]
        exact hstep
      exact ⟨Step.lDivertLand (s := s) a f ι κ v δ h' c hreach hfR hl htR hstepR, rfl, rfl⟩
  | lLeave a f κ v hf hl ht =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have htR : State.targetOf s a ≠ some v := by
        intro hbad
        have hbadD : State.targetOf (State.del s n) a = some v := by
          rw [targetOf_del_eq_of_vestigial h ha]
          exact hbad
        exact ht hbadD
      exact ⟨Step.lLeave (s := s) a f κ v hfR hl htR, rfl, rfl⟩
  | lUnload a f κ v o hf hl hg =>
      subst m
      have ha : a ≠ n := by intro hEq; subst a; exact hm rfl
      have hfR : lookup s.reg a = some f := by exact (lookup_del_cases (n := n) hf).2
      have hgR : ¬ State.relied s a := by
        intro hbad
        have hbadD : State.relied (State.del s n) a := by
          exact (relied_del_eq_of_vestigial h ha).mpr (by simpa [State.del] using hbad)
        exact hg hbadD
      exact ⟨Step.lUnload (s := s) a f κ v o hfR hl hgR, rfl, rfl⟩

/-! ## Lemma 54 step-local preservation lemmas -/

namespace Step

variable {s : State N K E V}

/-- **Lemma 54(1), registry form.**  A step changes the registry only at
the fiber it acts on. -/
theorem lookup_next_eq_of_ne (st : Step s) {m : N} (hm : m ≠ st.name) :
    lookup (Step.next st).reg m = lookup s.reg m := by
  rw [Step.factorization]
  rw [Step.edit_preserves_lookup_ne st (by simpa [Step.name] using hm)]
  exact Step.psi_preserves_lookup_ne st hm

/-- **Lemma 54(1), fiber form.**  A step changes no fiber it does not act
on. -/
theorem fiber_next_eq_of_ne (st : Step s) {m : N} (hm : m ≠ st.name) :
    ∀ f', lookup (Step.next st).reg m = some f' → lookup s.reg m = some f' := by
  intro f' h
  rw [lookup_next_eq_of_ne st hm] at h
  exact h

/-- A kind that does not write the ambient component of the full context.
In the faithful model the ambient is written by the three iterator rules and
by `L-Unload`; all other rules preserve it. -/
def PreservesAmbientKind (k : Full.StepKind) : Prop :=
  k ≠ Full.StepKind.lIter ∧ k ≠ Full.StepKind.lFinish ∧
    k ≠ Full.StepKind.lDivertLand ∧ k ≠ Full.StepKind.lUnload

/-- **Lemma 54(3), ambient half (faithful adaptation).**  Only iterator
rules and `L-Unload` move the ambient component of the full context. -/
theorem ambient_next_eq_of_preservesAmbientKind (st : Step s)
    (h : PreservesAmbientKind st.kind) :
    (Step.next st).ambient = s.ambient := by
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.next, Step.edit, Step.psi]
  | oRetire n f hf => simp [Step.next, Step.edit, Step.psi, hf]
  | oRemove n f o hf hl hchild => simp [Step.next, Step.edit, Step.psi]
  | lBegin n f v hf hl ht htable => simp [Step.next, Step.edit, Step.psi, hf]
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.next, Step.edit, Step.psi, hf]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.next, Step.edit, Step.psi, hf]
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lLeave n f κ v hf hl ht => simp [Step.next, Step.edit, Step.psi, hf]
  | lUnload n f κ v o hf hl hg =>
      simp [Step.kind, PreservesAmbientKind] at h

/-- **Lemma 54(3), ambient half for `Ψ`.**  The same preservation holds
when evaluating `Ψ` at an arbitrary state. -/
theorem psi_ambient_eq_of_preservesAmbientKind (st : Step s)
    (h : PreservesAmbientKind st.kind) :
    ∀ x, (Step.psi st x).ambient = x.ambient := by
  intro x
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.psi]
  | oRetire n f hf => simp [Step.psi]
  | oRemove n f o hf hl hchild => simp [Step.psi]
  | lBegin n f v hf hl ht htable => simp [Step.psi]
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.psi]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.psi]
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      simp [Step.kind, PreservesAmbientKind] at h
  | lLeave n f κ v hf hl ht => simp [Step.psi]
  | lUnload n f κ v o hf hl hg =>
      simp [Step.kind, PreservesAmbientKind] at h

/-- **Lemma 54(3), table half for `Ψ`.**  A `Ψ` that writes no table and is
not `L-Unload` leaves every registry unchanged.  (`L-Unload` writes the
recovered full-context effect in the faithful model, so it is excluded.) -/
theorem psi_reg_eq_of_not_writesTable (st : Step s)
    (h : ¬ Full.StepKind.writesTable st.kind)
    (hnot : st.kind ≠ Full.StepKind.lUnload) :
    ∀ x, (Step.psi st x).reg = x.reg := by
  intro x
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.psi]
  | oRetire n f hf => simp [Step.psi]
  | oRemove n f o hf hl hchild => simp [Step.psi]
  | lBegin n f v hf hl ht htable => simp [Step.psi]
  | lIter n f ι κ v ι' δ hh hreach hf hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lFinish n f ι κ v δ hh hreach hf hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lRaise n f ι κ v e hreach hf hl hstep => simp [Step.psi]
  | lDivertAbort n f ι κ v hreach hf hl ht => simp [Step.psi]
  | lDivertLand n f ι κ v δ hh c hreach hf hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lLeave n f κ v hf hl ht => simp [Step.psi]
  | lUnload n f κ v o hf hl hg =>
      simp [Step.kind] at hnot

/-- **Lemma 54(1), table form.**  A step whose `Ψ` writes no table (and is
not `L-Unload`) leaves the acting fiber's table unchanged. -/
theorem table_next_eq_of_not_writesTable (st : Step s)
    (h : ¬ Full.StepKind.writesTable st.kind)
    (hnot : st.kind ≠ Full.StepKind.lUnload) {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (Step.next st).reg st.name = some f') :
    f'.table = f.table := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
  | oRetire n f0 hf0 =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      have hf'eq : f' = { f0 with retired := true } := by
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        exact hf'.symm
      subst f'
      rfl
  | oRemove n f o hf0 hl hchild =>
      simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
  | lBegin n f0 v hf0 hl ht htable =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      have hf'eq : f' = { f0 with lc := .loading f0.comp.iter id v } := by
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        exact hf'.symm
      subst f'
      rfl
  | lIter n f ι κ v ι' δ hh hreach hf0 hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lFinish n f ι κ v δ hh hreach hf0 hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      have hf'eq : f' = { f0 with lc := .unloading κ v (some e) } := by
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        exact hf'.symm
      subst f'
      rfl
  | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      have hf'eq : f' = { f0 with lc := .unloading κ v none } := by
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        exact hf'.symm
      subst f'
      rfl
  | lDivertLand n f ι κ v δ hh c hreach hf0 hl ht hstep =>
      simp [Step.kind, Full.StepKind.writesTable] at h
  | lLeave n f0 κ v hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      have hf'eq : f' = { f0 with lc := .unloading κ v none } := by
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        exact hf'.symm
      subst f'
      rfl
  | lUnload n f κ v o hf0 hl hg =>
      simp [Step.kind] at hnot

/-- **Lemma 54(5), retired monotonicity.**  The retirement flag only
changes from `false` to `true`, and never back to `false`. -/
theorem retired_monotone (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (Step.next st).reg m = some f')
    (hret : f.retired = true) : f'.retired = true := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj =>
        simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
    | oRetire n f0 hf0 =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
    | oRemove n f o hf0 hl hchild =>
        simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
    | lBegin n f0 v hf0 hl ht htable =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lLeave n f0 κ v hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp [hret]
    | lUnload n f0 κ v o hf0 hl hg =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq,
          State.writeEffect_eq_of_lookup] at hf'
        rw [← hf']
        simp [hret]
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    rw [← hff]
    exact hret

/-- **Lemma 54(5), retired only by `O-Retire`.**  A retirement flag that
is newly true can only be written by `O-Retire` acting on that fiber. -/
theorem retired_changed_iff (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (Step.next st).reg m = some f')
    (hnot : f.retired = false) (hret : f'.retired = true) :
    st.name = m ∧ st.kind = Full.StepKind.oRetire := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj =>
        simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
    | oRetire n f0 hf0 =>
        simp [Step.name, Step.kind]
    | oRemove n f o hf0 hl hchild =>
        simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
    | lBegin n f0 v hf0 hl ht htable =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lLeave n f0 κ v hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
    | lUnload n f0 κ v o hf0 hl hg =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq,
          State.writeEffect_eq_of_lookup] at hf'
        rw [← hf'] at hret
        simp [hnot] at hret
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    rw [← hff] at hret
    rw [hnot] at hret
    cases hret

/-- **Lemma 54(1), registry form (alias).**  A step changes the registry
only at the fiber it acts on.  In the current model this is the direct
replacement for the legacy `Ostep`/`LstepT` disjunction. -/
theorem regStep (st : Step s) :
    ∀ m, m ≠ st.name → lookup (Step.next st).reg m = lookup s.reg m := by
  intro m hm
  exact lookup_next_eq_of_ne st hm

/-- **Lemma 54(3), ambient half (faithful adaptation).**  The old
`CoefCtx`-only statement “only `L-Unload` moves the ambient” does not hold
verbatim in the faithful full-context model, because iterator rules also
write a full-context effect.  This alias uses the faithful
`PreservesAmbientKind` side condition instead. -/
theorem ambient_next_eq_of_not_lUnload (st : Step s)
    (h : PreservesAmbientKind st.kind) :
    (Step.next st).ambient = s.ambient :=
  ambient_next_eq_of_preservesAmbientKind st h

/-- **Lemma 54(3), ambient half for `Ψ` (faithful adaptation).**  The same
adapted side condition for the `Ψ` map. -/
theorem psi_ambient_eq_of_not_lUnload (st : Step s)
    (h : PreservesAmbientKind st.kind) :
    ∀ x, (Step.psi st x).ambient = x.ambient :=
  psi_ambient_eq_of_preservesAmbientKind st h

/-- **Lemma 54(2).** The committed view changes only at `L-Begin` and
`L-Unload`; in particular it is constant while both old and new lifecycle
states are installed. -/
theorem viewOf_next_eq_of_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (Step.next st).reg st.name = some f')
    (hinst : f.lc.installed) (hinst' : f'.lc.installed) :
    f'.lc.viewOf = f.lc.viewOf := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
  | oRetire n f0 hf0 =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf']
  | oRemove n f o hf0 hl hchild =>
      simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
  | lBegin n f0 v hf0 hl ht htable =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf']
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lLeave n f0 κ v hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf']
      simp [Lifecycle.viewOf, hl]
  | lUnload n f0 κ v o hf0 hl hg =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq,
        State.writeEffect_eq_of_lookup] at hf'
      rw [← hf']
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'

/-- **Lemma 54(4), opening.**  An installed fiber can only come into
existence at `L-Begin` of that fiber. -/
theorem installed_next_of_not_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (Step.next st).reg st.name = some f')
    (hinst : ¬ f.lc.installed) (hinst' : f'.lc.installed) :
    st.kind = Full.StepKind.lBegin := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
  | oRetire n f0 hf0 =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      exact False.elim (hinst hinst')
  | oRemove n f o hf0 hl hchild =>
      simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
  | lBegin n f v hf0 hl ht htable => rfl
  | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lLeave n f0 κ v hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst
  | lUnload n f0 κ v o hf0 hl hg =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq,
        State.writeEffect_eq_of_lookup] at hf'
      rw [← hf'] at hinst'
      rw [hl] at hinst
      simp [Lifecycle.installed] at hinst

/-- **Lemma 54(4), closing.**  An installed fiber can only cease to be
installed at `L-Unload` of that fiber. -/
theorem not_installed_next_of_installed (st : Step s)
    {f f' : Fiber N K V E}
    (hf : lookup s.reg st.name = some f)
    (hf' : lookup (Step.next st).reg st.name = some f')
    (hinst : f.lc.installed) (hinst' : ¬ f'.lc.installed) :
    st.kind = Full.StepKind.lUnload := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
  | oRetire n f0 hf0 =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      exact False.elim (hinst' hinst)
  | oRemove n f o hf0 hl hchild =>
      simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
  | lBegin n f0 v hf0 hl ht htable =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
        State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lLeave n f0 κ v hf0 hl ht =>
      have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
      have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
      subst f
      simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
      rw [← hf'] at hinst'
      simp [Lifecycle.installed] at hinst'
  | lUnload n f κ v o hf0 hl hg => rfl

/-- **Lemma 54(5).** The component and parent fields are written once,
when the fiber is inserted; they never change afterward. -/
theorem comp_parent_next_eq (st : Step s) {m : N} {f f' : Fiber N K V E}
    (hf : lookup s.reg m = some f) (hf' : lookup (Step.next st).reg m = some f') :
    f'.comp = f.comp ∧ f'.parent = f.parent := by
  by_cases hm : m = st.name
  · subst m
    cases st with
    | oInsert n c p hn hp hdisj =>
        simp [Step.next, Step.edit, Step.psi, Step.name, hn] at hf
    | oRetire n f0 hf0 =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | oRemove n f o hf0 hl hchild =>
        simp [Step.next, Step.edit, Step.psi, Step.name, lookup_del_self] at hf'
    | lBegin n f0 v hf0 hl ht htable =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lIter n f0 ι κ v ι' δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lFinish n f0 ι κ v δ hh hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lRaise n f0 ι κ v e hreach hf0 hl hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lDivertAbort n f0 ι κ v hreach hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lDivertLand n f0 ι κ v δ hh c hreach hf0 hl ht hstep =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, hstep,
          State.writeEffect_eq_of_lookup, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lLeave n f0 κ v hf0 hl ht =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq] at hf'
        rw [← hf']
        simp
    | lUnload n f0 κ v o hf0 hl hg =>
        have hfn : lookup s.reg n = some f := by simpa [Step.name] using hf
        have hff : f = f0 := Option.some.inj (hfn.symm.trans hf0)
        subst f
        simp [Step.factorization, Step.edit, Step.psi, Step.name, hf0, lookup_set_eq,
          State.writeEffect_eq_of_lookup] at hf'
        rw [← hf']
        simp
  · have hlook := lookup_next_eq_of_ne st hm
    rw [hlook] at hf'
    have hff : f = f' := Option.some.inj (hf.symm.trans hf')
    subst f'
    simp

end Step

end Cordix
