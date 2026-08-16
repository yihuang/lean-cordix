import LeanCordix.TraceModel

/-
# Cordix — Lemma 56 support: renaming names injectively

This module contains the transport machinery for Lemma 56 (equivariance
under a bijection of names).  It defines the forward renaming of views,
lifecycle states, fibers, registries, and states along a function
`φ : N → M`, and proves that `lookup`, `sigmaOf`, `providerOf`, and
`targetOf` commute with the renaming when `φ` is injective.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Cordix

namespace Full

universe u

variable {N M K E : Type} [DecidableEq N] [DecidableEq M] [DecidableEq K]
  {V : K → Type u}

/-- A bijection of fiber names, given by two inverse functions. -/
structure NameEquiv (N M : Type) where
  fwd : N → M
  bwd : M → N
  fwd_bwd : ∀ n, bwd (fwd n) = n
  bwd_fwd : ∀ m, fwd (bwd m) = m

namespace NameEquiv

theorem fwd_injective (e : NameEquiv N M) : Function.Injective e.fwd := by
  intro a b h
  have hb := congrArg e.bwd h
  simpa [e.fwd_bwd] using hb

theorem bwd_injective (e : NameEquiv N M) : Function.Injective e.bwd := by
  intro a b h
  have hf := congrArg e.fwd h
  simpa [e.bwd_fwd] using hf

/-- The inverse bijection. -/
def symm (e : NameEquiv N M) : NameEquiv M N where
  fwd := e.bwd
  bwd := e.fwd
  fwd_bwd := e.bwd_fwd
  bwd_fwd := e.fwd_bwd

end NameEquiv

namespace Rename

/-- Rename an optional fiber name. -/
def option (φ : N → M) : Option N → Option M
  | none => none
  | some n => some (φ n)

/-- Rename a committed view. -/
def view (φ : N → M) (v : K → Option N) : K → Option M :=
  fun k => option φ (v k)

/-- Rename the name fields of a lifecycle state. -/
def lifecycle (φ : N → M) : Lifecycle N K V E → Lifecycle M K V E
  | .inactive o => .inactive o
  | .loading ι κ v => .loading ι κ (view φ v)
  | .active κ v => .active κ (view φ v)
  | .unloading κ v o => .unloading κ (view φ v) o

/-- Rename the name fields of a fiber. -/
def fiber (φ : N → M) (f : Fiber N K V E) : Fiber M K V E where
  comp := f.comp
  parent := option φ f.parent
  table := f.table
  retired := f.retired
  lc := lifecycle φ f.lc

/-- Rename the keys and name fields of a registry. -/
def registry (φ : N → M) : Registry N K V E → Registry M K V E :=
  List.map (fun p : N × Fiber N K V E => (φ p.1, fiber φ p.2))

/-- Rename the registry of a state; the ambient context is unchanged. -/
def state (φ : N → M) (s : State N K E V) : State M K E V where
  reg := registry φ s.reg
  ambient := s.ambient

theorem option_injective {φ : N → M} (hinj : Function.Injective φ) :
    Function.Injective (option φ) := by
  intro a b h
  cases a <;> cases b <;> simp [option] at h ⊢
  exact hinj h

/-- `lookup` commutes with renaming. -/
theorem lookup_rename (φ : N → M) (r : Registry N K V E) (n : N)
    (hinj : Function.Injective φ) :
    lookup (registry φ r) (φ n) = Option.map (fiber φ) (lookup r n) := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      by_cases hp : p.1 = n
      · simp [registry, lookup, hp]
      · have hφ : φ p.1 ≠ φ n := by
          intro hEq; exact hp (hinj hEq)
        simpa [registry, lookup, hp, hφ] using ih

theorem fold_rename_sigma (φ : N → M) (r : Registry N K V E) (k : K) :
    List.foldr (fun p acc => match p.2.lc with | .active _ _ => (p.2.table k).or acc | _ => acc) none
        (List.map (fun p : N × Fiber N K V E => (φ p.1, fiber φ p.2)) r)
    = List.foldr (fun p acc => match p.2.lc with | .active _ _ => (p.2.table k).or acc | _ => acc) none r := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      cases hlc : p.2.lc with
      | inactive o => simp [fiber, lifecycle, hlc]; exact ih
      | loading ι κ v => simp [fiber, lifecycle, hlc]; exact ih
      | active κ v => simp [fiber, lifecycle, hlc]; exact congrArg (fun x => (p.2.table k).or x) ih
      | unloading κ v o => simp [fiber, lifecycle, hlc]; exact ih

/-- `sigmaOf` is invariant under renaming: it reads only tables and
installedness, neither of which mentions names. -/
theorem sigmaOf_rename (φ : N → M) (r : Registry N K V E) :
    sigmaOf (registry φ r) = sigmaOf r := by
  funext k
  simp [sigmaOf, registry]
  exact fold_rename_sigma φ r k

theorem fold_rename_provider (φ : N → M) (r : Registry N K V E) (k : K) :
    List.foldr (fun p acc => match p.2.lc with | .active _ _ => if (p.2.table k).isSome then some p.1 else acc | _ => acc) none
        (List.map (fun p : N × Fiber N K V E => (φ p.1, fiber φ p.2)) r)
    = option φ (List.foldr (fun p acc => match p.2.lc with | .active _ _ => if (p.2.table k).isSome then some p.1 else acc | _ => acc) none r) := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      cases hlc : p.2.lc with
      | inactive o => simp [fiber, lifecycle, hlc]; exact ih
      | loading ι κ v => simp [fiber, lifecycle, hlc]; exact ih
      | active κ v =>
          simp [fiber, lifecycle, hlc]
          by_cases ht : (p.2.table k).isSome
          · simp [ht, option]
          · simp [ht, option]
            exact ih
      | unloading κ v o => simp [fiber, lifecycle, hlc]; exact ih

/-- `providerOf` maps by the renaming on names. -/
theorem providerOf_rename (φ : N → M) (r : Registry N K V E) (k : K) :
    providerOf (registry φ r) k = option φ (providerOf r k) := by
  unfold providerOf
  exact fold_rename_provider φ r k

/-- `targetOf` maps by the renaming on views. -/
theorem targetOf_rename (φ : N → M) (r : Registry N K V E) (n : N)
    (hinj : Function.Injective φ) :
    targetOf (registry φ r) (φ n) = Option.map (view φ) (targetOf r n) := by
  unfold targetOf
  rw [lookup_rename φ r n hinj]
  cases h : lookup r n with
  | none => rfl
  | some f =>
      simp only [Option.map]
      by_cases hc : f.retired = true ∨ ¬satisfies (sigmaOf r) f.comp.spec
      · have hc' : (fiber φ f).retired = true ∨
            ¬satisfies (sigmaOf (registry φ r)) (fiber φ f).comp.spec := by
          rcases hc with hret | hnotsat
          · left; simpa [fiber] using hret
          · right; intro hs
            have hs_r : satisfies (sigmaOf r) f.comp.spec := by
              simpa [fiber, sigmaOf_rename] using hs
            exact hnotsat hs_r
        simp only [if_pos hc, if_pos hc']
      · have hnotret : ¬ f.retired = true := fun hr => hc (Or.inl hr)
        have hsat : satisfies (sigmaOf r) f.comp.spec := by
          exact Classical.byContradiction (fun hs => hc (Or.inr hs))
        have hc' : ¬ ((fiber φ f).retired = true ∨
              ¬satisfies (sigmaOf (registry φ r)) (fiber φ f).comp.spec) := by
          intro hbad
          rcases hbad with hret | hnotsat
          · exact hnotret (by simpa [fiber] using hret)
          · exact hnotsat (by simpa [fiber, sigmaOf_rename] using hsat)
        rw [if_neg hc, if_neg hc']
        congr 1
        funext k
        by_cases hk : k ∈ f.comp.spec <;> simp [view, fiber, option, hk, providerOf_rename]

/-- Renaming a view forward and then backward is the identity. -/
theorem view_comp (e : NameEquiv N M) (v : K → Option N) :
    view e.bwd (view e.fwd v) = v := by
  funext k
  simp [view, option]
  cases h : v k <;> simp [h, e.fwd_bwd]

/-- Renaming a lifecycle forward and then backward is the identity. -/
theorem lifecycle_comp (e : NameEquiv N M) (lc : Lifecycle N K V E) :
    lifecycle e.bwd (lifecycle e.fwd lc) = lc := by
  cases lc <;> simp [lifecycle, view_comp]

/-- Renaming a fiber forward and then backward is the identity. -/
theorem fiber_comp (e : NameEquiv N M) (f : Fiber N K V E) :
    fiber e.bwd (fiber e.fwd f) = f := by
  cases f with
  | mk comp parent table retired lc =>
      cases parent <;> simp [fiber, lifecycle_comp, option, e.fwd_bwd]

/-- Renaming a registry forward and then backward is the identity. -/
theorem registry_comp (e : NameEquiv N M) (r : Registry N K V E) :
    registry e.bwd (registry e.fwd r) = r := by
  induction r with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk a f =>
          simp [registry, fiber_comp, e.fwd_bwd]
          rw [← List.map_map]
          exact ih

/-- Renaming a state forward and then backward is the identity. -/
theorem state_comp (e : NameEquiv N M) (s : State N K E V) :
    state e.bwd (state e.fwd s) = s := by
  cases s
  simp [state, registry_comp]

/-- Installedness is invariant under renaming. -/
theorem lifecycle_installed_iff (φ : N → M) (lc : Lifecycle N K V E) :
    (lifecycle φ lc).installed ↔ lc.installed := by
  cases lc <;> simp [lifecycle, Lifecycle.installed]

/-- The committed view of a renamed lifecycle is the renamed view. -/
theorem viewOf_lifecycle_rename (φ : N → M) (lc : Lifecycle N K V E) (k : K) :
    (lifecycle φ lc).viewOf k = option φ (lc.viewOf k) := by
  cases lc <;> simp [lifecycle, Lifecycle.viewOf, view, option]

/-- The withdrawal guard is equivariant under a bijection of names. -/
theorem relied_rename_iff (e : NameEquiv N M) (r : Registry N K V E) (n : N) :
    relied (registry e.fwd r) (e.fwd n) ↔ relied r n := by
  constructor
  · rintro ⟨n', k, f', hlook, hne, hinst, hv⟩
    have hlookR : Option.map (fiber e.fwd) (lookup r (e.bwd n')) = some f' := by
      have hlr := lookup_rename e.fwd r (e.bwd n') (NameEquiv.fwd_injective e)
      have hlr' : lookup (registry e.fwd r) n' = Option.map (fiber e.fwd) (lookup r (e.bwd n')) := by
        simpa [e.bwd_fwd n'] using hlr
      rw [← hlook]
      exact hlr'.symm
    cases hlr : lookup r (e.bwd n') with
    | none => simp [hlr] at hlookR
    | some f =>
        have hf : fiber e.fwd f = f' := by
          simpa [hlr] using hlookR
        have hn : e.bwd n' ≠ n := by
          intro hEq
          have : e.fwd (e.bwd n') = e.fwd n := by rw [hEq]
          rw [e.bwd_fwd n'] at this
          exact hne this
        refine ⟨e.bwd n', k, f, hlr, hn, ?_, ?_⟩
        · rw [← hf] at hinst
          simpa [fiber] using (lifecycle_installed_iff e.fwd f.lc).mp hinst
        · rw [← hf] at hv
          have hv0 : (lifecycle e.fwd f.lc).viewOf k = some (e.fwd n) := by
            simpa [fiber] using hv
          rw [viewOf_lifecycle_rename] at hv0
          exact option_injective (NameEquiv.fwd_injective e) hv0
  · rintro ⟨n', k, f, hlook, hne, hinst, hv⟩
    have hlookR : lookup (registry e.fwd r) (e.fwd n') = some (fiber e.fwd f) := by
      rw [lookup_rename e.fwd r n' (NameEquiv.fwd_injective e), hlook]
      rfl
    refine ⟨e.fwd n', k, fiber e.fwd f, hlookR, ?_, ?_, ?_⟩
    · intro hEq
      exact hne (NameEquiv.fwd_injective e hEq)
    · exact (lifecycle_installed_iff e.fwd f.lc).mpr hinst
    · change (lifecycle e.fwd f.lc).viewOf k = some (e.fwd n)
      rw [viewOf_lifecycle_rename]
      simp [hv, option]

end Rename


/-- Given a renamed lookup result, recover the original fiber and lookup. -/
theorem lookup_rename_state_some {s : State N K E V} (e : NameEquiv N M)
    {n' : M} {g : Fiber M K V E}
    (h : lookup (Rename.state e.fwd s).reg n' = some g) :
    ∃ f : Fiber N K V E,
      lookup s.reg (e.bwd n') = some f ∧ Rename.fiber e.fwd f = g := by
  have hlr := Rename.lookup_rename e.fwd s.reg (e.bwd n') (NameEquiv.fwd_injective e)
  have hlr' : lookup (Rename.state e.fwd s).reg n' =
      Option.map (Rename.fiber e.fwd) (lookup s.reg (e.bwd n')) := by
    simpa [Rename.state, e.bwd_fwd n'] using hlr
  rw [hlr'] at h
  cases hlook : lookup s.reg (e.bwd n') with
  | none => simp [hlook] at h
  | some f =>
      have hf : Rename.fiber e.fwd f = g :=
        Option.some.inj (by simpa [hlook] using h)
      exact ⟨f, rfl, hf⟩

/-- **Lemma 56, forward half.**  A bijection of names transports every
`Step` record: the transported record acts on the renamed fiber, has the
same rule kind, and lives at the renamed state. -/
theorem step_rename {s : State N K E V} (e : NameEquiv N M) (st : Step s) :
    ∃ st' : Step (Rename.state e.fwd s),
      st'.name = e.fwd st.name ∧ st'.kind = st.kind := by
  cases st with
  | oInsert a c p hn hp hdisj =>
      have hlookD : lookup (Rename.state e.fwd s).reg (e.fwd a) = none := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hn]
        rfl
      have hpD : ∀ n' ∈ Rename.option e.fwd p,
          ∃ f, lookup (Rename.state e.fwd s).reg n' = some f := by
        intro n' hn'
        cases p with
        | none => simp [Rename.option] at hn'
        | some b =>
            simp [Rename.option] at hn'
            rcases hp b (by simp) with ⟨f, hf⟩
            refine ⟨Rename.fiber e.fwd f, ?_⟩
            simp [Rename.state]
            rw [← hn']
            rw [Rename.lookup_rename e.fwd s.reg b (NameEquiv.fwd_injective e)]
            rw [hf]
            rfl
      have hdisjD : ∀ n' f, lookup (Rename.state e.fwd s).reg n' = some f →
          (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k') := by
        intro n' g hlook k hk k' hk'
        rcases lookup_rename_state_some e hlook with ⟨f0, hf0, hgf⟩
        rw [← hgf] at hk'
        exact hdisj (e.bwd n') f0 hf0 k hk k' hk'
      exact ⟨Step.oInsert (s := Rename.state e.fwd s) (e.fwd a) c
        (Rename.option e.fwd p) hlookD hpD hdisjD, rfl, rfl⟩
  | oRetire a f hf =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      exact ⟨Step.oRetire (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) hfD, rfl, rfl⟩
  | oRemove a f o hf hl hchild =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have hchildD : ∀ n' f', lookup (Rename.state e.fwd s).reg n' = some f' →
          f'.parent ≠ some (e.fwd a) := by
        intro n' g hlook
        rcases lookup_rename_state_some e hlook with ⟨f0, hf0, hgf⟩
        rw [← hgf]
        intro hparent
        have hparent0 : f0.parent = some a := by
          apply Rename.option_injective (NameEquiv.fwd_injective e)
          simpa [Rename.fiber, Rename.option] using hparent
        exact hchild (e.bwd n') f0 hf0 hparent0
      exact ⟨Step.oRemove (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) o hfD (by simp [Rename.fiber]; rw [hl]; rfl)
        hchildD, rfl, rfl⟩
  | lBegin a f v hf hl ht =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.view e.fwd v) := by
        simp [Rename.state]
        rw [Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [ht]
        rfl
      exact ⟨Step.lBegin (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) (Rename.view e.fwd v) hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD, rfl, rfl⟩
  | lIter a f ι κ v ι' δ hinv hreach hf hl ht hstep =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.view e.fwd v) := by
        simp [Rename.state]
        rw [Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [ht]
        rfl
      have hstepD : Cordix.Iterator.step ι (sigmaOf (Rename.state e.fwd s).reg) =
          Except.ok (δ, hinv, some ι') := by
        simpa [Rename.state, Rename.sigmaOf_rename e.fwd s.reg] using hstep
      exact ⟨Step.lIter (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) ι κ (Rename.view e.fwd v) ι' δ hinv hreach hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD hstepD, rfl, rfl⟩
  | lFinish a f ι κ v δ hinv hreach hf hl ht hstep =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.view e.fwd v) := by
        simp [Rename.state]
        rw [Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [ht]
        rfl
      have hstepD : Cordix.Iterator.step ι (sigmaOf (Rename.state e.fwd s).reg) =
          Except.ok (δ, hinv, none) := by
        simpa [Rename.state, Rename.sigmaOf_rename e.fwd s.reg] using hstep
      exact ⟨Step.lFinish (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) ι κ (Rename.view e.fwd v) δ hinv hreach hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD hstepD, rfl, rfl⟩
  | lRaise a f ι κ v e0 hreach hf hl hstep =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have hstepD : Cordix.Iterator.step ι (sigmaOf (Rename.state e.fwd s).reg) =
          Except.error e0 := by
        simpa [Rename.state, Rename.sigmaOf_rename e.fwd s.reg] using hstep
      exact ⟨Step.lRaise (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) ι κ (Rename.view e.fwd v) e0 hreach hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) hstepD, rfl, rfl⟩
  | lDivertAbort a f ι κ v hreach hf hl ht =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) ≠
          some (Rename.view e.fwd v) := by
        intro hbad
        have ht0 : targetOf s.reg a = some v := by
          have htp := Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)
          have hbad0 : Option.map (Rename.view e.fwd) (targetOf s.reg a) =
              some (Rename.view e.fwd v) := by
            simpa [Rename.state, htp] using hbad
          have view_inj : Function.Injective
              (Rename.view (N:=N) (M:=M) (K:=K) e.fwd) := by
            intro u w h
            apply funext
            intro k
            exact Rename.option_injective (NameEquiv.fwd_injective e) (congrFun h k)
          cases htarget : targetOf s.reg a with
          | none => simp [htarget] at hbad0
          | some v0 =>
              have hv0 : v0 = v := view_inj
                (Option.some.inj (by simpa [htarget] using hbad0))
              rw [hv0]
        exact ht ht0
      exact ⟨Step.lDivertAbort (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) ι κ (Rename.view e.fwd v) hreach hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD, rfl, rfl⟩
  | lDivertLand a f ι κ v δ hinv c hreach hf hl ht hstep =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) ≠
          some (Rename.view e.fwd v) := by
        intro hbad
        have ht0 : targetOf s.reg a = some v := by
          have htp := Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)
          have hbad0 : Option.map (Rename.view e.fwd) (targetOf s.reg a) =
              some (Rename.view e.fwd v) := by
            simpa [Rename.state, htp] using hbad
          have view_inj : Function.Injective
              (Rename.view (N:=N) (M:=M) (K:=K) e.fwd) := by
            intro u w h
            apply funext
            intro k
            exact Rename.option_injective (NameEquiv.fwd_injective e) (congrFun h k)
          cases htarget : targetOf s.reg a with
          | none => simp [htarget] at hbad0
          | some v0 =>
              have hv0 : v0 = v := view_inj
                (Option.some.inj (by simpa [htarget] using hbad0))
              rw [hv0]
        exact ht ht0
      have hstepD : Cordix.Iterator.step ι (sigmaOf (Rename.state e.fwd s).reg) =
          Except.ok (δ, hinv, c) := by
        simpa [Rename.state, Rename.sigmaOf_rename e.fwd s.reg] using hstep
      exact ⟨Step.lDivertLand (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) ι κ (Rename.view e.fwd v) δ hinv c hreach hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD hstepD, rfl, rfl⟩
  | lLeave a f κ v hf hl ht =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have htD : targetOf (Rename.state e.fwd s).reg (e.fwd a) ≠
          some (Rename.view e.fwd v) := by
        intro hbad
        have ht0 : targetOf s.reg a = some v := by
          have htp := Rename.targetOf_rename e.fwd s.reg a (NameEquiv.fwd_injective e)
          have hbad0 : Option.map (Rename.view e.fwd) (targetOf s.reg a) =
              some (Rename.view e.fwd v) := by
            simpa [Rename.state, htp] using hbad
          have view_inj : Function.Injective
              (Rename.view (N:=N) (M:=M) (K:=K) e.fwd) := by
            intro u w h
            apply funext
            intro k
            exact Rename.option_injective (NameEquiv.fwd_injective e) (congrFun h k)
          cases htarget : targetOf s.reg a with
          | none => simp [htarget] at hbad0
          | some v0 =>
              have hv0 : v0 = v := view_inj
                (Option.some.inj (by simpa [htarget] using hbad0))
              rw [hv0]
        exact ht ht0
      exact ⟨Step.lLeave (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) κ (Rename.view e.fwd v) hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) htD, rfl, rfl⟩
  | lUnload a f κ v o hf hl hg =>
      have hfD : lookup (Rename.state e.fwd s).reg (e.fwd a) =
          some (Rename.fiber e.fwd f) := by
        simp [Rename.state]
        rw [Rename.lookup_rename e.fwd s.reg a (NameEquiv.fwd_injective e)]
        rw [hf]
        rfl
      have hgD : ¬ relied (Rename.state e.fwd s).reg (e.fwd a) := by
        intro hbad
        have hg0 : relied s.reg a :=
          (Rename.relied_rename_iff e s.reg a).mp (by simpa [Rename.state] using hbad)
        exact hg hg0
      exact ⟨Step.lUnload (s := Rename.state e.fwd s) (e.fwd a)
        (Rename.fiber e.fwd f) κ (Rename.view e.fwd v) o hfD
        (by simp [Rename.fiber]; rw [hl]; rfl) hgD, rfl, rfl⟩

end Full

end Cordix
