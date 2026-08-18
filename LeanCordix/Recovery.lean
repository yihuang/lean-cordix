import LeanCordix.Approx

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-- If every reachable iterator and lifecycle accumulator is write-confined,
then a step that is confined at its source remains `PsiConfinedAt` after
recovering another fiber and folding through `≈`-equivalent states. -/
theorem Step.psiConfinedAt_of_confined {s x : State N K E V} (st : Step s) {n : N}
    (hst : st.name ≠ n)
    (hconf : Step.Confined st)
    (hconf_iter : ∀ f, lookup s.reg st.name = some f →
        ∀ ι, Iterator.Reachable f.comp.iter ι → ConfinedIterator ι f.comp.prov)
    (hconf_acc : ∀ f, lookup s.reg st.name = some f →
        ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov)
    (hnodup_s : NodupKeys s.reg)
    (hx_approx : State.Approx (State.recover s n) x)
    (hfull : State.fullCtx (State.recover s n) = State.fullCtx x)
    (hdom : (lookup (State.recover s n).reg st.name).isSome ↔
      (lookup x.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup (State.recover s n).reg st.name = some gx →
      lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov)
    (hnrec : NodupKeys (State.recover s n).reg) (hnx : NodupKeys x.reg) :
    Step.PsiConfinedAt st (State.recover s n) x := by
  cases st with
  | oInsert m c p hn hp hdisj => trivial
  | oRetire m f hf => trivial
  | oRemove m f o hf hl hchild => trivial
  | lBegin m f v hf hl ht htable => trivial
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lRaise m f ι κ v e hreach hf hl hstep => trivial
  | lDivertAbort m f ι κ v hreach hf hl ht => trivial
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      intro δ' hx hy
      rcases hx with ⟨h', c', hx⟩
      rcases hy with ⟨h'', c'', hy⟩
      have hx' : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ', h, c) :=
        ⟨h', c', hx⟩
      have hι : ∀ f', lookup s.reg m = some f' → ConfinedIterator ι f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        simpa [Step.name] using hconf_iter f hf ι hreach
      have hconf_y : ConfinedEffect (State.recover s n) m δ' := by
        exact State.confinedEffect_of_confinedIterator_of_recover
          (s := s) (m := m) (n := n) (ι := ι) (δ := δ') (δ₀ := δ)
          hmn hnodup_s hconf hι hx'
      have hdom_m : (lookup (State.recover s n).reg m).isSome ↔
          (lookup x.reg m).isSome := by simpa [Step.name] using hdom
      have hprov_m : ∀ gy gz, lookup (State.recover s n).reg m = some gy →
          lookup x.reg m = some gz → gy.comp.prov = gz.comp.prov := by
        simpa [Step.name] using hprov
      have hconf_x : ConfinedEffect x m δ' := by
        exact State.confinedEffect_transfer_of_approx
          (y := State.recover s n) (z := x) (m := m) (δ := δ')
          hx_approx hfull hdom_m hprov_m hnrec hnx hconf_y
      exact ⟨hconf_y, hconf_x⟩
  | lLeave m f κ v hf hl ht => trivial
  | lUnload m f κ v o hf hl hg =>
      have hmn : m ≠ n := by simpa [Step.name] using hst
      have hκ : ∀ f', lookup s.reg m = some f' → ConfinedAcc κ f'.comp.prov := by
        intro f' hf'
        have hf'f : f' = f := lookup_eq_of_nodup hnodup_s hf' hf
        subst f'
        have hκ' : ConfinedAcc (Lifecycle.acc f.lc) f.comp.prov := by simpa [Step.name] using hconf_acc f hf
        simpa [Lifecycle.acc, hl] using hκ'
      have hconf_y : ConfinedEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
        exact State.confinedEffect_of_confinedAcc_of_recover
          (s := s) (m := m) (n := n) (κ := κ) (δ₀ := κ (State.fullCtx s))
          hmn hnodup_s hconf hκ
      have hκ_eq : κ (State.fullCtx (State.recover s n)) = κ (State.fullCtx x) := by
        rw [hfull]
      have hconf_x : ConfinedEffect x m (κ (State.fullCtx x)) := by
        have hconf_x' : ConfinedEffect x m (κ (State.fullCtx (State.recover s n))) := by
          exact State.confinedEffect_transfer_of_approx
            (y := State.recover s n) (z := x) (m := m)
            (δ := κ (State.fullCtx (State.recover s n)))
            hx_approx hfull (by simpa [Step.name] using hdom) (by simpa [Step.name] using hprov) hnrec hnx hconf_y
        simpa [hκ_eq] using hconf_x'
      exact ⟨hconf_y, hconf_x⟩

/-- A faithful `Step.psi` preserves `≈` when the input full contexts agree
and the acting name has the same presence in both input states. -/
theorem Step.psi_preserves_approx {s x y : State N K E V} (st : Step s)
    (h : State.Approx x y)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hdom : (lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup x.reg st.name = some gx →
      lookup y.reg st.name = some gy → gx.comp.prov = gy.comp.prov) :
    State.Approx (Step.psi st x) (Step.psi st y) := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi] using h
  | oRetire n f hf => simpa [Step.psi] using h
  | oRemove n f o hf hl hchild => simpa [Step.psi] using h
  | lBegin n f v hf hl ht htable => simpa [Step.psi] using h
  | lIter n f ι κ v ι' δ h' hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lFinish n f ι κ v δ h' hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi] using h
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi] using h
  | lDivertLand n f ι κ v δ h' c hreach hf hl ht hstep =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, h]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_approx h δ' hdom' hprov'
  | lLeave n f κ v hf hl ht => simpa [Step.psi] using h
  | lUnload n f κ v o hf hl hg =>
      have hdom' : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome := by
        simpa [Step.name] using hdom
      have hprov' : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
          gx.comp.prov = gy.comp.prov := by
        simpa [Step.name] using hprov
      by_cases hx : (lookup x.reg n).isSome
      · have hy : (lookup y.reg n).isSome := hdom'.mp hx
        rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
        rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
        have hκ : κ (State.fullCtx x) = κ (State.fullCtx y) := by rw [hfull]
        simp [Step.psi, hfx, hfy, hκ]
        exact State.writeEffect_preserves_approx h (κ (State.fullCtx y)) hdom' hprov'
      · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom'.mpr hy)
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
        simp [Step.psi, hxn, hyn, h]

/-- A faithful `Step.psi` preserves `fullCtx` equality when the recomputed
step is confined at both input states. -/
theorem Step.psi_preserves_fullCtx {s x y : State N K E V} (st : Step s)
    (hfull : State.fullCtx x = State.fullCtx y)
    (hdom : (lookup x.reg st.name).isSome ↔ (lookup y.reg st.name).isSome)
    (hprov : ∀ gx gy, lookup x.reg st.name = some gx →
      lookup y.reg st.name = some gy → gx.comp.prov = gy.comp.prov)
    (hnx : NodupKeys x.reg) (hny : NodupKeys y.reg)
    (hconf : Step.PsiConfinedAt st x y) :
    State.fullCtx (Step.psi st x) = State.fullCtx (Step.psi st y) := by
  cases st with
  | oInsert n c p hn hp hdisj => simpa [Step.psi, hfull]
  | oRetire n f hf => simpa [Step.psi, hfull]
  | oRemove n f o hf hl hchild => simpa [Step.psi, hfull]
  | lBegin n f v hf hl ht htable => simpa [Step.psi, hfull]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lRaise n f ι κ v e hreach hf hl hstep => simpa [Step.psi, hfull]
  | lDivertAbort n f ι κ v hreach hf hl ht => simpa [Step.psi, hfull]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      cases hstep_x : Iterator.step ι (State.fullCtx x) with
      | error e =>
          have hstep_y : Iterator.step ι (State.fullCtx y) = .error e := by
            rw [← hfull, hstep_x]
          simp [Step.psi, hstep_x, hstep_y, hfull]
      | ok p =>
          rcases p with ⟨δ', h'', c'⟩
          have hstep_y : Iterator.step ι (State.fullCtx y) = .ok (δ', h'', c') := by
            rw [← hfull, hstep_x]
          have hconf' := hconf δ' ⟨h'', c', hstep_x⟩ ⟨h'', c', hstep_y⟩
          simp [Step.psi, hstep_x, hstep_y]
          exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hconf'.2
  | lLeave n f κ v hf hl ht => simpa [Step.psi, hfull]
  | lUnload n f κ v o hf hl hg =>
      have hconf' := hconf
      by_cases hx : (lookup x.reg n).isSome
      · have hy : (lookup y.reg n).isSome := hdom.mp hx
        rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
        rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
        simp only [Step.psi, hfx, hfy]
        rw [← hfull]
        have hcy : ConfinedEffect y n (κ (State.fullCtx x)) := by
          simpa [hfull] using hconf'.2
        exact State.writeEffect_preserves_fullCtx_of_confined hnx hny hconf'.1 hcy
      · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
        have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
        have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
        simp [Step.psi, hxn, hyn, hfull]

/-- **Faithful Equation (52) up to `≈`.** For every rule except `O-Remove`,
the `edit` half writes only control fields. -/
theorem Step.edit_approx_psi_of_ne_remove {s : State N K E V} (st : Step s)
    (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.Approx (Step.next st) (Step.psi st s) := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      constructor
      · simp [Step.next, Step.edit, Step.psi]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hn, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, lookup_set_ne, hmn]
  | oRetire n f hf =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | oRemove n f o hf hl hchild =>
      simp [Step.kind] at hno
  | lBegin n f v hf hl ht htable =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lRaise n f ι κ v e hreach hf hl hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, hstep, State.tableAt, hf, State.lookup_writeEffect_eq hf δ, lookup_set_ne, hmn]
  | lLeave n f κ v hf hl ht =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, lookup_set_ne, hmn]
  | lUnload n f κ v o hf hl hg =>
      constructor
      · simp [Step.next, Step.edit, Step.psi, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq]
        · simp [Step.next, Step.edit, Step.psi, State.tableAt, hf, State.writeEffect_eq_of_lookup hf (κ (State.fullCtx s)), lookup_set_eq, lookup_set_ne, hmn]

/-- `recover` preserves `≈` when the two input states agree on the lookup at
`n` and on the full context.  This is the version needed for `edit`-away
steps: the edit does not touch `n`, so recovery at `n` sees the same fiber
and the same full context. -/
theorem State.recover_preserves_approx_of_lookup_fullCtx {x y : State N K E V} {n : N}
    (h : State.Approx x y)
    (hlook : lookup x.reg n = lookup y.reg n)
    (hfull : State.fullCtx x = State.fullCtx y) :
    State.Approx (State.recover x n) (State.recover y n) := by
  by_cases hn : (lookup y.reg n).isSome
  · rcases Option.isSome_iff_exists.mp hn with ⟨f, hf⟩
    have hx : lookup x.reg n = some f := by rw [hlook]; exact hf
    cases hlc : f.lc with
    | inactive o =>
        simpa [State.recover, hx, hf, hlc] using h
    | loading i κ v =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_loading_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_loading_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
    | active κ v =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_active_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_active_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
    | unloading κ v o =>
        have hxrec : State.recover x n =
            ⟨set x.reg n { f with table := fun _ => none }, (κ (State.fullCtx x)).1⟩ := by
          exact State.recover_unloading_eq hx hlc
        have hyrec : State.recover y n =
            ⟨set y.reg n { f with table := fun _ => none }, (κ (State.fullCtx y)).1⟩ := by
          exact State.recover_unloading_eq hf hlc
        rw [hxrec, hyrec]
        constructor
        · simp [hfull]
        · intro m
          by_cases hmn : m = n
          · subst m
            simp [State.tableAt, lookup_set_eq]
          · simpa [State.tableAt, lookup_set_ne, hmn] using h.tables m
  · have hnone : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hn
    have hxnone : lookup x.reg n = none := by rw [hlook]; exact hnone
    simpa [State.recover, hxnone, hnone] using h

/-- For a non-`O-Remove` step acting on a fiber other than `n`, the `edit`
half does not change the full context. -/
theorem State.fullCtx_next_eq_fullCtx_psi_of_ne_remove {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name) (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.fullCtx (Step.next st) = State.fullCtx (Step.psi st s) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi,
          rawSigma_set_empty_fiber_of_not_mem hn]
  | oRetire m f hf =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_retired_eq]
  | oRemove m f o hf hl hchild =>
      exact False.elim (hno (by simp [Step.kind]))
  | lBegin m f v hf hl ht htable =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lRaise m f ι κ v e hreach hf hl hstep =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hpsi : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) s =
          State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hf' : lookup (State.writeEffect s m δ).reg m =
          some ({ f with table := splitTable f.comp.prov δ.2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf δ
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']
  | lLeave m f κ v hf hl ht =>
      apply Prod.ext
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf]
      · simp [State.fullCtx, Step.next, Step.edit, Step.psi, hf,
          rawSigma_set_lc_eq]
  | lUnload m f κ v o hf hl hg =>
      have hpsi : Step.psi (Step.lUnload m f κ v o hf hl hg) s =
          State.writeEffect s m (κ (State.fullCtx s)) := by
        simp [Step.psi, hf]
      have hf' : lookup (State.writeEffect s m (κ (State.fullCtx s))).reg m =
          some ({ f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2 } : Fiber N K V E) := by
        exact State.lookup_writeEffect_eq hf (κ (State.fullCtx s))
      simp [State.fullCtx] at hpsi hf'
      simp [State.fullCtx, Step.next, Step.edit, hpsi, hf', rawSigma_set_lc_eq hf']

/-- For a non-`O-Remove` step acting on a fiber other than `n`, the `edit`
half does not touch `n` and does not change the full context, so recovery at
`n` commutes with the `edit` up to `≈`. -/
theorem State.recover_next_approx_recover_psi_of_ne_remove {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name) (hno : st.kind ≠ Full.StepKind.oRemove) :
    State.Approx (State.recover (Step.next st) n) (State.recover (Step.psi st s) n) := by
  apply State.recover_preserves_approx_of_lookup_fullCtx
  · exact Step.edit_approx_psi_of_ne_remove st hno
  · cases st with
    | oInsert m c p hn hp hdisj =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hn, lookup_set_ne, hmn, Ne.symm hmn]
    | oRetire m f hf =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | oRemove m f o hf hl hchild =>
        exact False.elim (hno (by simp [Step.kind]))
    | lBegin m f v hf hl ht htable =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lRaise m f ι κ v e hreach hf hl hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lDivertAbort m f ι κ v hreach hf hl ht =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hstep, hf, State.lookup_writeEffect_eq hf δ,
          lookup_set_ne, hmn, Ne.symm hmn]
    | lLeave m f κ v hf hl ht =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, lookup_set_ne, hmn, Ne.symm hmn]
    | lUnload m f κ v o hf hl hg =>
        have hmn : n ≠ m := by simpa [Step.name] using hne
        simp [Step.next, Step.edit, Step.psi, hf, State.lookup_writeEffect_eq hf (κ (State.fullCtx s)),
          lookup_set_ne, hmn, Ne.symm hmn]
  · exact State.fullCtx_next_eq_fullCtx_psi_of_ne_remove st hne hno

/-- A faithful `L-Iter` step on `n` is invisible to `State.recover` up to
`≈`: the new inverse recovers the full context that the accumulator already
knew. -/
theorem Step.recover_self_lIter_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {ι' : Iterator (Ctx K V) E} {δ : Ctx K V}
    {h : Ctx K V → Ctx K V}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n = some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, some ι'))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .loading ι' (κ ∘ h) v }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .loading ι' (κ ∘ h) v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · -- ambient: `(κ ∘ h) (fullCtx next) = κ (fullCtx s)`
    simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · -- tables: both recoveries empty `n`'s table
    intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-Finish` step on `n` is invisible to `State.recover` up to
`≈`. -/
theorem Step.recover_self_lFinish_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V} {h : Ctx K V → Ctx K V}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n = some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, none))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .active (κ ∘ h) v }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .active (κ ∘ h) v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-DivertLand` step on `n` is invisible to `State.recover` up
to `≈`. -/
theorem Step.recover_self_lDivertLand_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {δ : Ctx K V} {h : Ctx K V → Ctx K V}
    {c : Option (Iterator (Ctx K V) E)}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n ≠ some v)
    (hstep : Iterator.step ι (State.fullCtx s) = .ok (δ, h, c))
    (hnodup : NodupKeys s.reg) (hconf : ConfinedEffect s n δ) :
    State.Approx
      (State.recover (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)) n)
      (State.recover s n) := by
  let f' : Fiber N K V E := { f with table := splitTable f.comp.prov δ.2 }
  have hf_write : lookup (State.writeEffect s n δ).reg n = some f' := by
    simp [State.writeEffect, hf, f', lookup_set_eq]
  have hwitness : h δ = State.fullCtx s := by
    have hw' := f.comp.wit hreach (State.fullCtx s)
    unfold Iterator.Witnessed at hw'
    rw [hstep] at hw'
    simpa using hw'
  have hfull_next : State.fullCtx
      (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)) = δ := by
    have hpsi : Step.psi (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep) s =
        State.writeEffect s n δ := by
      simp [Step.psi, hstep]
    rw [Step.next, hpsi]
    have hfull_edit : State.fullCtx
        (Step.edit (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)
          (State.writeEffect s n δ)) =
        State.fullCtx (State.writeEffect s n δ) := by
      unfold State.fullCtx
      apply Prod.ext
      · simp [Step.edit, hf_write]
      · have hset : rawSigma
            (set (State.writeEffect s n δ).reg n
              { f' with lc := .unloading (κ ∘ h) v none }) =
            rawSigma (State.writeEffect s n δ).reg := by
          apply rawSigma_set_lc_eq hf_write
        simpa [Step.edit, hf_write] using hset
    rw [hfull_edit]
    exact State.fullCtx_writeEffect_of_confined hnodup hconf
  have hf_next : lookup (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg n =
      some ({ f' with lc := .unloading (κ ∘ h) v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf, f', lookup_set_eq]
  constructor
  · simp [State.recover, hf_next, hf, hl, hfull_next, hwitness, Function.comp]
  · intro x
    by_cases hxn : x = n
    · subst x
      simp [State.recover, hf_next, hf, hl, State.tableAt, lookup_set_eq]
    · have hlook : lookup (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg x =
          lookup s.reg x := by
        simp [Step.next, Step.edit, Step.psi, hstep, State.writeEffect, hf,
          lookup_set_eq, lookup_set_ne, hxn, Ne.symm hxn]
      simp [State.recover, hf_next, hf, hl, State.tableAt, hxn,
        lookup_set_ne, Ne.symm hxn]
      rw [hlook]

/-- A faithful `L-Unload` step on `n` is invisible to `State.recover` up to
`≈`, provided the accumulator withdraws the fiber's own table. -/
theorem Step.recover_self_lUnload_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {κ : Ctx K V → Ctx K V} {v : K → Option N} {o : Option E}
    (hf : lookup s.reg n = some f) (hl : f.lc = .unloading κ v o)
    (hg : ¬ relied s.reg n)
    (hno_prov : ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none) :
    State.Approx
      (State.recover (Step.next (Step.lUnload n f κ v o hf hl hg)) n)
      (State.recover s n) := by
  let δ : Ctx K V := κ (State.fullCtx s)
  have hwrite : State.writeEffect s n δ =
      ⟨set s.reg n { f with table := splitTable f.comp.prov δ.2 }, δ.1⟩ := by
    simp [State.writeEffect, hf]
  have hnext_eq : Step.next (Step.lUnload n f κ v o hf hl hg) =
      ⟨set s.reg n { f with table := splitTable f.comp.prov δ.2, lc := .inactive o }, δ.1⟩ := by
    rw [Step.next, Step.psi, hf]
    rw [hwrite]
    simp [Step.edit, lookup_set_eq, set_set_eq]
  have hrecover_next : State.recover (Step.next (Step.lUnload n f κ v o hf hl hg)) n =
      Step.next (Step.lUnload n f κ v o hf hl hg) := by
    rw [hnext_eq]
    simp [State.recover, lookup_set_eq]
  have hrecover_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_unloading_eq hf hl
  rw [hrecover_next, hnext_eq, hrecover_s]
  constructor
  · rfl
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq]
      funext k
      by_cases hk : k ∈ f.comp.prov
      · simp [splitTable, hk]
        change (κ (State.fullCtx s)).2 k = none
        exact hno_prov k hk
      · simp [splitTable, hk]
    · simp [State.tableAt, lookup_set_ne, hmn, Ne.symm hmn]

/-- A faithful `O-Insert` step on `n` is invisible to `State.recover` up to
`≈`: inserting an empty inactive fiber is the same as having no fiber. -/
theorem Step.recover_self_oInsert_approx {s : State N K E V} {n : N}
    {c : Component K V E} {p : Option N}
    (hn : lookup s.reg n = none)
    (hp : ∀ n' ∈ p, ∃ f, lookup s.reg n' = some f)
    (hdisj : ∀ n' f, lookup s.reg n' = some f →
      (∀ k ∈ c.prov, ∀ k' ∈ f.comp.prov, k ≠ k')) :
    State.Approx (State.recover (Step.next (Step.oInsert n c p hn hp hdisj)) n)
      (State.recover s n) := by
  have hs : State.recover s n = s := by
    simp [State.recover, hn]
  have hnext : Step.next (Step.oInsert n c p hn hp hdisj) =
      ⟨set s.reg n (Fiber.mk c p (fun _ => none) false (.inactive none)), s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi]
  rw [hs, hnext]
  simp [State.recover, lookup_set_eq]
  constructor
  · rfl
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, hn, lookup_set_eq]
    · simp [State.tableAt, hn, lookup_set_ne, hmn]

/-- A faithful `L-Begin` step on `n` is invisible to `State.recover` up to
`≈`, because `L-Begin` can only start from an inactive fiber whose table is
empty. -/
theorem Step.recover_self_lBegin_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .inactive none)
    (ht : targetOf s.reg n = some v) (htable : f.table = fun _ => none) :
    State.Approx (State.recover (Step.next (Step.lBegin n f v hf hl ht htable)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lBegin n f v hf hl ht htable) =
      ⟨set s.reg n { f with lc := .loading f.comp.iter id v }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hf_next : lookup (Step.next (Step.lBegin n f v hf hl ht htable)).reg n =
      some ({ f with lc := .loading f.comp.iter id v } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n = s := by
    simp [State.recover, hf, hl]
  have hrec_next : State.recover (Step.next (Step.lBegin n f v hf hl ht htable)) n =
      ⟨set (Step.next (Step.lBegin n f v hf hl ht htable)).reg n
        ({ f with lc := .loading f.comp.iter id v, table := fun _ => none } : Fiber N K V E),
        (State.fullCtx (Step.next (Step.lBegin n f v hf hl ht htable))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [State.fullCtx, rawSigma_set_lc_eq]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, hf, lookup_set_eq, set_set_eq, htable]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-Raise` step on `n` is invisible to `State.recover` up to
`≈`: it only changes the lifecycle to unloading, keeping the same
accumulator and the same table. -/
theorem Step.recover_self_lRaise_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N} {e : E}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (hstep : Iterator.step ι (State.fullCtx s) = .error e) :
    State.Approx (State.recover (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep) =
      ⟨set s.reg n { f with lc := .unloading κ v (some e) }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg n =
      some ({ f with lc := .unloading κ v (some e) } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_loading_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)) n =
      ⟨set (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)).reg n
        ({ f with lc := .unloading κ v (some e), table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lRaise n f ι κ v e hreach hf hl hstep)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-DivertAbort` step on `n` is invisible to `State.recover`
up to `≈`: it only changes the lifecycle to unloading. -/
theorem Step.recover_self_lDivertAbort_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {ι : Iterator (Ctx K V) E} {κ : Ctx K V → Ctx K V}
    {v : K → Option N}
    (hreach : Iterator.Reachable f.comp.iter ι)
    (hf : lookup s.reg n = some f) (hl : f.lc = .loading ι κ v)
    (ht : targetOf s.reg n ≠ some v) :
    State.Approx (State.recover (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht) =
      ⟨set s.reg n { f with lc := .unloading κ v none }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg n =
      some ({ f with lc := .unloading κ v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_loading_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)) n =
      ⟨set (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)).reg n
        ({ f with lc := .unloading κ v none, table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lDivertAbort n f ι κ v hreach hf hl ht)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `L-Leave` step on `n` is invisible to `State.recover` up to
`≈`: it only changes an active lifecycle to unloading. -/
theorem Step.recover_self_lLeave_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E} {κ : Ctx K V → Ctx K V} {v : K → Option N}
    (hf : lookup s.reg n = some f) (hl : f.lc = .active κ v)
    (ht : targetOf s.reg n ≠ some v) :
    State.Approx (State.recover (Step.next (Step.lLeave n f κ v hf hl ht)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.lLeave n f κ v hf hl ht) =
      ⟨set s.reg n { f with lc := .unloading κ v none }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.lLeave n f κ v hf hl ht)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_lc_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.lLeave n f κ v hf hl ht)).reg n =
      some ({ f with lc := .unloading κ v none } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  have hrec_s : State.recover s n =
      ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
    exact State.recover_active_eq hf hl
  have hrec_next : State.recover (Step.next (Step.lLeave n f κ v hf hl ht)) n =
      ⟨set (Step.next (Step.lLeave n f κ v hf hl ht)).reg n
        ({ f with lc := .unloading κ v none, table := fun _ => none } : Fiber N K V E),
        (κ (State.fullCtx (Step.next (Step.lLeave n f κ v hf hl ht)))).1⟩ := by
    simpa [State.recover, hf_next]
  rw [hrec_next, hrec_s, hnext]
  constructor
  · simp [hfull]
  · intro m
    by_cases hmn : m = n
    · subst m
      simp [State.tableAt, lookup_set_eq, set_set_eq]
    · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- A faithful `O-Retire` step on `n` is invisible to `State.recover` up to
`≈`: retirement is a control field that `≈` forgets. -/
theorem Step.recover_self_oRetire_approx {s : State N K E V} {n : N}
    {f : Fiber N K V E}
    (hf : lookup s.reg n = some f) :
    State.Approx (State.recover (Step.next (Step.oRetire n f hf)) n)
      (State.recover s n) := by
  have hnext : Step.next (Step.oRetire n f hf) =
      ⟨set s.reg n { f with retired := true }, s.ambient⟩ := by
    simp [Step.next, Step.edit, Step.psi, hf]
  have hfull : State.fullCtx (Step.next (Step.oRetire n f hf)) =
      State.fullCtx s := by
    unfold State.fullCtx
    rw [hnext]
    apply Prod.ext
    · rfl
    · simpa using rawSigma_set_retired_eq hf
  rw [hnext] at hfull
  have hf_next : lookup (Step.next (Step.oRetire n f hf)).reg n =
      some ({ f with retired := true } : Fiber N K V E) := by
    simp [Step.next, Step.edit, Step.psi, hf, lookup_set_eq]
  cases hlc : f.lc with
  | inactive o =>
      have hrec_s : State.recover s n = s := by
        simp [State.recover, hf, hlc]
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          Step.next (Step.oRetire n f hf) := by
        simp [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · rfl
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, hf, lookup_set_eq]
        · simp [State.tableAt, hf, lookup_set_ne, hmn]
  | loading i κ v =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_loading_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]
  | active κ v =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_active_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]
  | unloading κ v o =>
      have hrec_s : State.recover s n =
          ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ := by
        exact State.recover_unloading_eq hf hlc
      have hrec_next : State.recover (Step.next (Step.oRetire n f hf)) n =
          ⟨set (Step.next (Step.oRetire n f hf)).reg n
            ({ f with retired := true, table := fun _ => none } : Fiber N K V E),
            (κ (State.fullCtx (Step.next (Step.oRetire n f hf)))).1⟩ := by
        simpa [State.recover, hf_next, hlc]
      rw [hrec_next, hrec_s, hnext]
      constructor
      · simp [hfull]
      · intro m
        by_cases hmn : m = n
        · subst m
          simp [State.tableAt, lookup_set_eq, set_set_eq]
        · simp [State.tableAt, lookup_set_ne, hmn, set_set_eq]

/-- For a self-step, the extra withdrawal condition needed by `L-Unload`: the
accumulator must leave every key in the fiber's own provision absent.  For
all other self-steps this predicate is trivially true. -/
def Step.SelfWithdrawsAt {s : State N K E V} (st : Step s) : Prop :=
  match st with
  | Step.lUnload n f κ v o hf hl hg =>
      ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none
  | _ => True

/-- A total self-step recovery lemma for every non-`O-Remove` rule.  The
iterator rules additionally require duplicate-free registries and confined
writes; `L-Unload` requires the withdrawal condition captured by
`SelfWithdrawsAt`. -/
theorem Step.recover_self_approx_of_confined {s : State N K E V} (st : Step s)
    {n : N}
    (hname : st.name = n)
    (hno : st.kind ≠ Full.StepKind.oRemove)
    (hnodup : NodupKeys s.reg)
    (hconf : Step.Confined st)
    (hw : Step.SelfWithdrawsAt st) :
    State.Approx (State.recover (Step.next st) n) (State.recover s n) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_oInsert_approx hn hp hdisj
  | oRetire m f hf =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_oRetire_approx hf
  | oRemove m f o hf hl hchild =>
      exact False.elim (hno (by simp [Step.kind]))
  | lBegin m f v hf hl ht htable =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lBegin_approx hf hl ht htable
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lIter_approx hreach hf hl ht hstep hnodup hconf'
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lFinish_approx hreach hf hl ht hstep hnodup hconf'
  | lRaise m f ι κ v e hreach hf hl hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lRaise_approx hreach hf hl hstep
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lDivertAbort_approx hreach hf hl ht
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hconf' : ConfinedEffect s n δ := hconf
      exact Step.recover_self_lDivertLand_approx hreach hf hl ht hstep hnodup hconf'
  | lLeave m f κ v hf hl ht =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      exact Step.recover_self_lLeave_approx hf hl ht
  | lUnload m f κ v o hf hl hg =>
      have hm : m = n := by simpa [Step.name] using hname
      subst m
      have hw' : ∀ k ∈ f.comp.prov, (κ (State.fullCtx s)).2 k = none := by
        simpa [Step.SelfWithdrawsAt] using hw
      exact Step.recover_self_lUnload_approx hf hl hg hw'

/-- Wrapper for presence agreement, used to avoid an elaboration issue with
local functions returning `Iff` directly. -/
def SamePresence {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  (lookup (State.recover s n).reg st.name).isSome ↔ (lookup x.reg st.name).isSome

/-- Wrapper for provision agreement, used to avoid an elaboration issue with
local functions returning `Iff` directly. -/
def SameProvision {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  ∀ gx gy, lookup (State.recover s n).reg st.name = some gx →
    lookup x.reg st.name = some gy → gx.comp.prov = gy.comp.prov

/-- Combined presence/provision agreement for the fiber acted on by `st`.
This packages `SamePresence` and `SameProvision` into one side condition. -/
def SameFiber {N : Type} [DecidableEq N] {K : Type} [DecidableEq K]
    {V : K → Type u} {E : Type}
    (s : State N K E V) (n : N) (st : Step s) (x : State N K E V) : Prop :=
  match lookup (State.recover s n).reg st.name, lookup x.reg st.name with
  | some gx, some gy => gx.comp.prov = gy.comp.prov
  | none, none => True
  | _, _ => False

/-- `SameFiber` implies `SamePresence`. -/
theorem samePresence_of_sameFiber {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} (hf : SameFiber s n st x) : SamePresence s n st x := by
  unfold SamePresence
  unfold SameFiber at hf
  cases hrec : lookup (State.recover s n).reg st.name with
  | none =>
      cases hx : lookup x.reg st.name with
      | none => simp [hrec, hx]
      | some gy => simp [hrec, hx] at hf
  | some gx =>
      cases hx : lookup x.reg st.name with
      | none => simp [hrec, hx] at hf
      | some gy => simp [hrec, hx, hf]

/-- `SameFiber` implies `SameProvision`. -/
theorem sameProvision_of_sameFiber {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} (hf : SameFiber s n st x) : SameProvision s n st x := by
  intro gx gy hgx hgy
  unfold SameFiber at hf
  rw [hgx, hgy] at hf
  exact hf

/-- `SamePresence` and `SameProvision` together imply `SameFiber`. -/
theorem sameFiber_of_samePresence_sameProvision {s : State N K E V} {n : N}
    {st : Step s} {x : State N K E V}
    (hdom : SamePresence s n st x) (hprov : SameProvision s n st x) :
    SameFiber s n st x := by
  unfold SameFiber
  by_cases hx : (lookup (State.recover s n).reg st.name).isSome
  · have hy : (lookup x.reg st.name).isSome := hdom.mp hx
    rcases Option.isSome_iff_exists.mp hx with ⟨gx, hgx⟩
    rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
    simp [hgx, hgy]
    exact hprov gx gy hgx hgy
  · have hxn : lookup (State.recover s n).reg st.name = none :=
      Option.not_isSome_iff_eq_none.mp hx
    have hy : ¬ (lookup x.reg st.name).isSome := by
      intro hy
      exact hx (hdom.mpr hy)
    have hyn : lookup x.reg st.name = none := Option.not_isSome_iff_eq_none.mp hy
    simp [hxn, hyn]

/-- `SameFiber` is `SameFiberAt` after recovering `n`. -/
theorem sameFiber_eq_sameFiberAt {s : State N K E V} {n : N} {st : Step s}
    {x : State N K E V} : SameFiber s n st x = SameFiberAt (State.recover s n) x st.name := by
  rfl

end Cordix
