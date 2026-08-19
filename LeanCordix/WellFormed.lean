import LeanCordix.Basic
import LeanCordix.Step
import LeanCordix.Trace

/-!
# LeanCordix.WellFormed — Definition 58 and Theorem 59 (Preservation)

This module ports the registry well-formedness metatheory from the deleted
legacy full-calculus file into the current faithful full-context model.

Definition 58 has four clauses:

1. parent pointers land in the registry;
2. provisions of distinct fibers are disjoint;
3. an installed fiber's committed view is total on its specification and
   names registered fibers;
4. a committed view names only installed fibers.

`WellFormedBase` is the shape-only part (clauses 1–2).  `WellFormed` is the
full Definition 58.  The main result is `WellFormed.preserved`: every
current `Step.next` preserves well-formedness.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Definition 58: well-formedness -/

/-- **Definition 58, clauses (1)–(2).**  The shape invariant of a registry:
parent pointers land in the registry, and the provisions of distinct fibers
are disjoint.  (Clauses (3)–(4) are in `WellFormed` below.) -/
structure WellFormedBase (r : Registry N K V E) : Prop where
  parentOk : ∀ n f, lookup r n = some f → ∀ m ∈ f.parent,
    ∃ f', lookup r m = some f'
  provDisj : ∀ n f n' f', lookup r n = some f → lookup r n' = some f' →
    n ≠ n' → ∀ k ∈ f.comp.prov, ∀ k' ∈ f'.comp.prov, k ≠ k'

/-- **Definition 58.**  A registry is well formed when its names are
duplicate-free, (1) parent pointers land, (2) provisions of distinct fibers
are disjoint, (3) an installed fiber's committed view is total on its
specification and names registered fibers, and (4) a committed view names
only installed fibers. -/
structure WellFormed (r : Registry N K V E) : Prop where
  nodupKeys : NodupKeys r
  parentOk : ∀ n f, lookup r n = some f → ∀ m ∈ f.parent,
    ∃ f', lookup r m = some f'
  provDisj : ∀ n f n' f', lookup r n = some f → lookup r n' = some f' →
    n ≠ n' → ∀ k ∈ f.comp.prov, ∀ k' ∈ f'.comp.prov, k ≠ k'
  viewTotal : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k ∈ f.comp.spec, ∃ m, f.lc.viewOf k = some m ∧ ∃ g, lookup r m = some g
  viewInstalled : ∀ n f, lookup r n = some f → f.lc.installed →
    ∀ k ∈ f.comp.spec, ∀ m, f.lc.viewOf k = some m →
    ∃ g, lookup r m = some g ∧ g.lc.installed

/-- Project `WellFormed` to its first two clauses. -/
theorem WellFormed.toBase {r : Registry N K V E} (hwf : WellFormed r) : WellFormedBase r :=
  ⟨hwf.parentOk, hwf.provDisj⟩

/-! ## Lookup transfer for pointwise update and deletion -/

theorem lookup_set_cases {r : Registry N K V E} {n m : N}
    {f f' : Fiber N K V E} (h : lookup (set r n f) m = some f') :
    (m = n ∧ f' = f) ∨ (m ≠ n ∧ lookup r m = some f') := by
  by_cases hmn : m = n
  · left
    subst m
    rw [lookup_set_eq] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · right
    exact ⟨hmn, by rwa [lookup_set_ne r n m f hmn] at h⟩

omit [DecidableEq K] in
theorem lookup_del_cases {r : Registry N K V E} {n m : N} {f' : Fiber N K V E}
    (h : lookup (del r n) m = some f') :
    m ≠ n ∧ lookup r m = some f' := by
  refine ⟨fun hmn => by rw [hmn, lookup_del_self] at h; simp at h, ?_⟩
  by_cases hmn : m = n
  · rw [hmn, lookup_del_self] at h; simp at h
  · rwa [lookup_del_ne (r := r) (n := n) (m := m) hmn] at h

/-- Removal does not introduce old keys. -/
theorem key_not_mem_del {r : Registry N K V E} {n : N} {p : N}
    (hn : p ∉ r.map (fun q => q.1)) :
    p ∉ (del r n).map (fun q => q.1) := by
  revert hn
  induction r with
  | nil =>
      intro hn h
      simp [del] at h
  | cons q rest ih =>
      intro hn h
      by_cases hq : q.1 = n
      · rw [show del (q :: rest) n = del rest n by simp [del, hq]] at h
        have hnq : p ∉ rest.map (fun q => q.1) := by
          intro h'
          exact hn (by simp [h'])
        exact ih hnq h
      · simp [del, hq] at h
        rcases h with hEq | hIn
        · exact hn (by simp [hEq])
        · have hnq : p ∉ rest.map (fun q => q.1) := by
            intro h'
            exact hn (by simp [h'])
          exact ih hnq (by
            rw [List.mem_map]
            rcases hIn with ⟨x, hx⟩
            exact ⟨(p, x), hx, rfl⟩)

/-! ## Preservation of clauses (1)–(2) under `set` and `del` -/

/-- Pointwise update at an existing name preserves `WellFormedBase` when
the component and the parent are unchanged. -/
theorem wellFormedBase_set (hwf : WellFormedBase r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hp : old.parent = new.parent) : WellFormedBase (set r n new) := by
  constructor
  · intro m g hm x hx
    obtain ⟨g₂, hg₂⟩ : ∃ g₂, lookup r x = some g₂ := by
      rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact hwf.parentOk n old h x (hp.symm ▸ (hg ▸ hx))
      · exact hwf.parentOk m g hg x hx
    by_cases hxn : x = n
    · subst hxn
      exact ⟨new, lookup_set_eq r _ new⟩
    · rw [lookup_set_ne r n x new hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    have toR : ∀ a α (ha : lookup (set r n new) a = some α),
        ∃ β, lookup r a = some β ∧ β.comp = α.comp := by
      intro a α ha
      rcases lookup_set_cases ha with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · subst heq; subst hg
        exact ⟨old, h, hc⟩
      · exact ⟨α, hg, rfl⟩
    obtain ⟨β, hb, hβ⟩ := toR m g hm
    obtain ⟨β', hb', hβ'⟩ := toR m' g' hm'
    have hk₁ : k ∈ β.comp.prov := by rw [hβ]; exact hk
    have hk₂ : k' ∈ β'.comp.prov := by rw [hβ']; exact hk'
    exact hwf.provDisj m β m' β' hb hb' hne k hk₁ k' hk₂

/-- Pointwise update at a fresh name preserves `WellFormedBase`. -/
theorem wellFormedBase_setFresh (hwf : WellFormedBase r) {n : N} {c : Component K V E}
    {p : Option N} {fresh : Fiber N K V E}
    (hnone : lookup r n = none) (hcomp : fresh.comp = c)
    (hpar : fresh.parent = p) (hp : ∀ x ∈ p, ∃ g, lookup r x = some g)
    (hdisj : ∀ m g, lookup r m = some g →
      ∀ k ∈ c.prov, ∀ k' ∈ g.comp.prov, k ≠ k') :
    WellFormedBase (set r n fresh) := by
  constructor
  · intro m g hm x hx
    have hgr : lookup r m = some g ∨ (m = n ∧ g = fresh) := by
      rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne, hg⟩
      · exact .inr ⟨heq, hg⟩
      · exact .inl hg
    have hland : ∃ g₂, lookup r x = some g₂ := by
      rcases hgr with hg | ⟨heq, hg⟩
      · exact hwf.parentOk m g hg x hx
      · subst heq; subst hg
        rw [hpar] at hx
        exact hp x hx
    obtain ⟨g₂, hg₂⟩ := hland
    by_cases hxn : x = n
    · subst hxn
      exact ⟨fresh, lookup_set_eq r _ fresh⟩
    · rw [lookup_set_ne r n x fresh hxn]
      exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    by_cases hmn : m = n
    · rw [hmn, lookup_set_eq] at hm
      have hgf : g = fresh := (Option.some.inj hm).symm
      rw [hgf, hcomp] at hk
      have hg' : lookup r m' = some g' := by
        rcases lookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd (hmn.trans heq.symm) hne
        · exact hg
      exact hdisj m' g' hg' k hk k' hk'
    · have hmOld : lookup r m = some g := by
        rcases lookup_set_cases hm with ⟨heq, hg⟩ | ⟨hne', hg⟩
        · exact absurd heq hmn
        · exact hg
      by_cases hmn' : m' = n
      · rw [hmn', lookup_set_eq] at hm'
        have hgf : g' = fresh := (Option.some.inj hm').symm
        rw [hgf, hcomp] at hk'
        exact fun heq => hdisj m g hmOld k' hk' k hk heq.symm
      · have hmOld' : lookup r m' = some g' := by
          rcases lookup_set_cases hm' with ⟨heq, hg⟩ | ⟨hne', hg⟩
          · exact absurd heq hmn'
          · exact hg
        exact hwf.provDisj m g m' g' hmOld hmOld' hne k hk k' hk'

/-- Removal preserves `WellFormedBase` when no fiber points at the removed
name. -/
theorem wellFormedBase_del (hwf : WellFormedBase r) {n : N}
    (hchild : ∀ m g, lookup r m = some g → g.parent ≠ some n) :
    WellFormedBase (del r n) := by
  constructor
  · intro m g hm x hx
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hne, hg⟩
    obtain ⟨g₂, hg₂⟩ := hwf.parentOk m g hg x hx
    have hxn : x ≠ n := by
      intro heq; subst heq
      simp only [Option.mem_def] at hx
      exact hchild m g hg hx
    rw [lookup_del_ne (r := r) (n := n) (m := x) hxn]
    exact ⟨g₂, hg₂⟩
  · intro m g m' g' hm hm' hne k hk k' hk'
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨_, hg⟩
    have hc' := lookup_del_cases (n := n) hm'
    rcases hc' with ⟨_, hg'⟩
    exact hwf.provDisj m g m' g' hg hg' hne k hk k' hk'

/-- **Theorem 59, clauses (1)–(2), current faithful `Step.next`.**  If the
source registry is `WellFormedBase`, every current step reaches a
`WellFormedBase` registry. -/
theorem wellFormedBase_preserved {s : State N K E V} (st : Step s)
    (hwf : WellFormedBase s.reg) : WellFormedBase (Step.next st).reg := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simpa [Step.next, Step.psi, Step.edit] using
        wellFormedBase_setFresh hwf hn rfl rfl hp hdisj
  | oRetire n f hf =>
      let new : Fiber N K V E := { f with retired := true }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormedBase_set (old := f) (new := new) hwf hf rfl rfl
  | oRemove n f o hf hl hchild =>
      simpa [Step.next, Step.psi, Step.edit] using
        wellFormedBase_del hwf hchild
  | lBegin n f v hf hl ht htable =>
      let new : Fiber N K V E := { f with lc := .loading f.comp.iter id v }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormedBase_set (old := f) (new := new) hwf hf rfl rfl
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hnext_reg :
          (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormedBase_set hwf hf rfl rfl
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hnext_reg :
          (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormedBase_set hwf hf rfl rfl
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormedBase_set (old := f) (new := new) hwf hf rfl rfl
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormedBase_set (old := f) (new := new) hwf hf rfl rfl
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hnext_reg :
          (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormedBase_set hwf hf rfl rfl
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormedBase_set (old := f) (new := new) hwf hf rfl rfl
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hnext_reg :
          (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf,
          lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormedBase_set hwf hf rfl rfl

/-! ## Target-view helpers used by full preservation -/

/-- **Theorem 63 (Eq. 58), faithful full-context form.**  A fiber begins a
transition only where its dependencies are provided: `target ≠ ⊥` gives a
live, non-retired fiber whose specification is satisfied by the active
sigma. -/
theorem satisfies_of_target {r : Registry N K V E} {n : N} {v : K → Option N}
    (ht : targetOf r n = some v) :
    ∃ f : Fiber N K V E, lookup r n = some f ∧ ¬ f.retired = true
      ∧ satisfies (sigmaOf r) f.comp.spec := by
  unfold targetOf at ht
  cases hl : lookup r n with
  | none => rw [hl] at ht; exact absurd ht (by simp)
  | some f =>
      rw [hl] at ht
      simp only [] at ht
      by_cases hc : f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec
      · rw [if_pos hc] at ht; exact absurd ht (by simp)
      · rw [if_neg hc] at ht
        refine ⟨f, rfl, fun hret => hc (Or.inl hret),
          Classical.byContradiction fun hsat => hc (Or.inr hsat)⟩

/-- If the coeffect context provides a key, then some active fiber is its
provider. -/
theorem providerOf_isSome_of_sigmaOf_isSome {r : Registry N K V E} {k : K} :
    (sigmaOf r k).isSome → (providerOf r k).isSome := by
  induction r with
  | nil => simp [sigmaOf, providerOf]
  | cons p rest ih =>
      intro h
      cases hlc : p.2.lc with
      | inactive _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)
      | loading _ _ _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)
      | active _ _ =>
          by_cases htbl : (p.2.table k).isSome
          · simp [providerOf, hlc, htbl]
          · simpa [providerOf, hlc, htbl] using ih (by simpa [sigmaOf, hlc, htbl] using h)
      | unloading _ _ _ => simpa [providerOf, hlc] using ih (by simpa [sigmaOf, hlc] using h)

/-- The name returned by `providerOf` is a key of the registry. -/
theorem providerOf_mem_keys {r : Registry N K V E} {k : K} {m : N}
    (h : providerOf r k = some m) : m ∈ r.map (fun p => p.1) := by
  induction r with
  | nil => simp [providerOf] at h
  | cons p rest ih =>
      cases hlc : p.2.lc with
      | inactive _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩
      | loading _ _ _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩
      | active _ _ =>
          simp [providerOf, hlc] at h
          by_cases htbl : (p.2.table k).isSome
          · simp [htbl] at h
            rw [List.mem_map]
            exact ⟨p, by simp [h]⟩
          · simp [htbl] at h
            have hm := ih h
            rw [List.mem_map] at hm
            rcases hm with ⟨x, hx, hfst⟩
            rw [List.mem_map]
            exact ⟨x, by simp [hx], hfst⟩
      | unloading _ _ _ =>
          simp [providerOf, hlc] at h
          have hm := ih h
          rw [List.mem_map] at hm
          rcases hm with ⟨x, hx, hfst⟩
          rw [List.mem_map]
          exact ⟨x, by simp [hx], hfst⟩

/-- A provider is an active fiber present in the registry. -/
theorem providerOf_some_lookup_active {r : Registry N K V E} {k : K} {m : N}
    (hn : NodupKeys r) (h : providerOf r k = some m) :
    ∃ g : Fiber N K V E, lookup r m = some g ∧ ∃ κ v, g.lc = .active κ v := by
  induction r with
  | nil => simp [providerOf] at h
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
        rw [List.nodup_cons] at hn
        exact hn.2
      cases hlc : p.2.lc with
      | inactive _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg
      | loading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg
      | active κ v =>
          simp [providerOf, hlc] at h
          by_cases htbl : (p.2.table k).isSome
          · simp [htbl] at h
            have hpm : p.1 = m := h
            refine ⟨p.2, by simp [lookup, hpm], κ, v, ?_⟩
            exact hlc
          · simp [htbl] at h
            rcases ih hnrest h with ⟨g, hg, hgact⟩
            have hpm : p.1 ≠ m := by
              intro hEq
              have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
              change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
              rw [List.nodup_cons] at hn
              exact hn.1 (by simpa [hEq] using hm)
            refine ⟨g, ?_, hgact⟩
            simpa [lookup, hpm] using hg
      | unloading _ _ _ =>
          simp [providerOf, hlc] at h
          rcases ih hnrest h with ⟨g, hg, hgact⟩
          have hpm : p.1 ≠ m := by
            intro hEq
            have hm : m ∈ rest.map (fun q => q.1) := providerOf_mem_keys h
            change ((p.1 :: rest.map (fun q => q.1)).Nodup) at hn
            rw [List.nodup_cons] at hn
            exact hn.1 (by simpa [hEq] using hm)
          refine ⟨g, ?_, hgact⟩
          simpa [lookup, hpm] using hg

/-- If `targetOf r n = some v`, then `v` is the provider map on the
component's specification. -/
theorem targetOf_view_eq {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hl : lookup r n = some f) (ht : targetOf r n = some v) :
    ∀ k ∈ f.comp.spec, v k = providerOf r k := by
  intro k hk
  unfold targetOf at ht
  rw [hl] at ht
  change ((if f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec then none
    else some (fun k => if k ∈ f.comp.spec then providerOf r k else none)) = some v) at ht
  by_cases hc : f.retired = true ∨ ¬ satisfies (sigmaOf r) f.comp.spec
  · rw [if_pos hc] at ht
    simp at ht
  · rw [if_neg hc] at ht
    have hv : v = fun k => if k ∈ f.comp.spec then providerOf r k else none :=
      (Option.some.inj ht).symm
    rw [hv]
    simp [hk]

/-- The target view of a fiber is total on its specification and names
installed fibers (well-formedness clauses (3)–(4) at `L-Begin`). -/
theorem targetOf_view_installed {r : Registry N K V E} {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hn : NodupKeys r) (hl : lookup r n = some f)
    (ht : targetOf r n = some v) :
    (∀ k ∈ f.comp.spec, v k = providerOf r k)
      ∧ (∀ k ∈ f.comp.spec, ∃ m, v k = some m ∧ ∃ g, lookup r m = some g)
      ∧ (∀ k ∈ f.comp.spec, ∀ m, v k = some m →
          ∃ g, lookup r m = some g ∧ g.lc.installed) := by
  have hsat : satisfies (sigmaOf r) f.comp.spec := by
    rcases satisfies_of_target ht with ⟨g, hg, _, hsat⟩
    have hfg : f = g := Option.some.inj (hl.symm.trans hg)
    rw [hfg]
    exact hsat
  refine ⟨targetOf_view_eq hl ht, ?_, ?_⟩
  · intro k hk
    rw [targetOf_view_eq hl ht k hk]
    have hsome : (sigmaOf r k).isSome := hsat k hk
    have hprov : (providerOf r k).isSome := providerOf_isSome_of_sigmaOf_isSome hsome
    rcases Option.isSome_iff_exists.mp hprov with ⟨m, hm⟩
    rcases providerOf_some_lookup_active hn hm with ⟨g, hg, hgact⟩
    exact ⟨m, hm, g, hg⟩
  · intro k hk m hvm
    rw [targetOf_view_eq hl ht k hk] at hvm
    rcases providerOf_some_lookup_active hn hvm with ⟨g, hg, κ, vg, hlc⟩
    exact ⟨g, hg, by rw [hlc]; trivial⟩

/-! ## Full preservation (Theorem 59, all clauses) -/

/-- A pointwise update at an existing name preserves full well-formedness
when the update keeps the component, the parent, and the committed view, and
does not newly install the fiber. -/
theorem wellFormed_set_viewSame (hwf : WellFormed r) {n : N} {old new : Fiber N K V E}
    (h : lookup r n = some old) (hc : old.comp = new.comp)
    (hp : old.parent = new.parent)
    (hinst : new.lc.installed → old.lc.installed)
    (hinst' : old.lc.installed → new.lc.installed)
    (hview : ∀ k, new.lc.viewOf k = old.lc.viewOf k) :
    WellFormed (set r n new) := by
  have hb := wellFormedBase_set hwf.toBase h hc hp
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hk_old : k ∈ old.comp.spec := by simpa [hc] using hk
      have hold : old.lc.installed := hinst hinst_m
      rcases hwf.viewTotal n old h hold k hk_old with ⟨p, hv, hlp⟩
      refine ⟨p, ?_, ?_⟩
      · rw [hview k]; exact hv
      · by_cases hpn : p = n
        · subst p; exact ⟨new, lookup_set_eq r n new⟩
        · rw [lookup_set_ne r n p new hpn]; exact hlp
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hk_old : k ∈ old.comp.spec := by simpa [hc] using hk
      have hold : old.lc.installed := hinst hinst_m
      have hv_old : old.lc.viewOf k = some p := by
        rw [hview k] at hvm
        exact hvm
      rcases hwf.viewInstalled n old h hold k hk_old p hv_old with ⟨q, hq, hqinst⟩
      by_cases hpn : p = n
      · subst p
        exact ⟨new, lookup_set_eq r n new, hinst_m⟩
      · rw [lookup_set_ne r n p new hpn]
        exact ⟨q, hq, hqinst⟩
    · rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      by_cases hpn : p = n
      · subst p
        have hqold : q = old := Option.some.inj (hq.symm.trans h)
        have hold_n : old.lc.installed := by simpa [hqold] using hqinst
        exact ⟨new, lookup_set_eq r n new, hinst' hold_n⟩
      · rw [lookup_set_ne r n p new hpn]
        exact ⟨q, hq, hqinst⟩

/-- `O-Insert` preserves full well-formedness. -/
theorem wellFormed_setFreshFull (hwf : WellFormed r) {n : N} {c : Component K V E}
    {p : Option N} {fresh : Fiber N K V E}
    (hnone : lookup r n = none) (hcomp : fresh.comp = c)
    (hpar : fresh.parent = p) (hp : ∀ x ∈ p, ∃ g, lookup r x = some g)
    (hdisj : ∀ m g, lookup r m = some g →
      ∀ k ∈ c.prov, ∀ k' ∈ g.comp.prov, k ≠ k')
    (hfresh : fresh.lc = .inactive none) :
    WellFormed (set r n fresh) := by
  have hb := wellFormedBase_setFresh hwf.toBase hnone hcomp hpar hp hdisj
  constructor
  · exact nodupKeys_set r n fresh hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      rw [hfresh] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨fresh, lookup_set_eq r n fresh⟩
      · rw [lookup_set_ne r n p fresh hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      rw [hfresh] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      have hpn : p ≠ n := by
        intro heq; subst p
        rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨q', hq', hq'inst⟩
        rw [hnone] at hq'
        simp at hq'
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p fresh hpn]
      exact hq

/-- `O-Remove` preserves full well-formedness. -/
theorem wellFormed_delFull (hwf : WellFormed r) {n : N} {f : Fiber N K V E}
    {o : Option E} (h : lookup r n = some f) (hl : f.lc = .inactive o)
    (hchild : ∀ m g, lookup r m = some g → g.parent ≠ some n) :
    WellFormed (del r n) := by
  have hb := wellFormedBase_del hwf.toBase hchild
  constructor
  · exact nodupKeys_del hwf.nodupKeys n
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hmn, hg⟩
    rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
    refine ⟨p, hv, ?_⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      rcases hwf.viewInstalled m g hg hinst_m k hk n hv with ⟨gn, hgn, hgninst⟩
      have hgn_f : gn = f := Option.some.inj (hgn.symm.trans h)
      rw [hgn_f, hl] at hgninst
      unfold Lifecycle.installed at hgninst
      cases hgninst
    rw [lookup_del_ne (r := r) (n := n) (m := p) hpn]
    exact hlp
  · intro m g hm hinst_m k hk p hvm
    have hc := lookup_del_cases (n := n) hm
    rcases hc with ⟨hmn, hg⟩
    have hpn : p ≠ n := by
      intro heq; subst p
      rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨gn, hgn, hgninst⟩
      have hgn_f : gn = f := Option.some.inj (hgn.symm.trans h)
      rw [hgn_f, hl] at hgninst
      unfold Lifecycle.installed at hgninst
      cases hgninst
    rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
    refine ⟨q, ?_, hqinst⟩
    rw [lookup_del_ne (r := r) (n := n) (m := p) hpn]
    exact hq

/-- `L-Begin` preserves full well-formedness: the target view is total on
the specification and names installed fibers. -/
theorem wellFormed_lBegin (hwf : WellFormed r) {n : N} {f : Fiber N K V E}
    {v : K → Option N} (hf : lookup r n = some f) (hl : f.lc = .inactive none)
    (ht : targetOf r n = some v) :
    WellFormed (set r n { f with lc := .loading f.comp.iter id v }) := by
  let new : Fiber N K V E := { f with lc := .loading f.comp.iter id v }
  have hb : WellFormedBase (set r n new) :=
    wellFormedBase_set (old := f) (new := new) hwf.toBase hf rfl rfl
  have htn := targetOf_view_installed hwf.nodupKeys hf ht
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hkf : k ∈ f.comp.spec := by simpa using hk
      rcases htn.2.1 k hkf with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
    · rcases hwf.viewTotal m g hg hinst_m k hk with ⟨p, hv, hlp⟩
      refine ⟨p, hv, ?_⟩
      by_cases hpn : p = n
      · subst p; exact ⟨new, lookup_set_eq r n new⟩
      · rw [lookup_set_ne r n p new hpn]; exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg⟩ | ⟨hmn, hg⟩
    · subst m; subst g
      have hkf : k ∈ f.comp.spec := by simpa using hk
      change v k = some p at hvm
      have hvmv : v k = some p := hvm
      have hpn : p ≠ n := by
        intro heq; subst p
        rcases htn.2.2 k hkf n hvmv with ⟨q, hq, hqinst⟩
        have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
        rw [hq_f, hl] at hqinst
        unfold Lifecycle.installed at hqinst
        cases hqinst
      rcases htn.2.2 k hkf p hvmv with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq
    · have hpn : p ≠ n := by
        intro heq; subst p
        rcases hwf.viewInstalled m g hg hinst_m k hk n hvm with ⟨q, hq, hqinst⟩
        have hq_f : q = f := Option.some.inj (hq.symm.trans hf)
        rw [hq_f, hl] at hqinst
        unfold Lifecycle.installed at hqinst
        cases hqinst
      rcases hwf.viewInstalled m g hg hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq

/-- `L-Unload` preserves full well-formedness: the guard `¬ relied` keeps
other committed views from naming the now-inactive fiber.  The new fiber may
also have a changed table (the faithful `ψ` half of `L-Unload` writes it
before `edit` deactivates the fiber), so this lemma is stated with an
arbitrary `new` that agrees with `old` on component and parent and is
`inactive o`. -/
theorem wellFormed_lUnload (hwf : WellFormed r) {n : N} {old new : Fiber N K V E}
    {o : Option E} (h : lookup r n = some old)
    (hcomp : old.comp = new.comp) (hpar : old.parent = new.parent)
    (hnew : new.lc = .inactive o) (hg : ¬ relied r n) :
    WellFormed (set r n new) := by
  have hb : WellFormedBase (set r n new) :=
    wellFormedBase_set (old := old) (new := new) hwf.toBase h hcomp hpar
  constructor
  · exact nodupKeys_set r n new hwf.nodupKeys
  · exact hb.parentOk
  · exact hb.provDisj
  · intro m g hm hinst_m k hk
    rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
    · subst m; subst g
      rw [hnew] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · rcases hwf.viewTotal m g hg' hinst_m k hk with ⟨p, hv, hlp⟩
      have hpn : p ≠ n := by
        intro heq; subst p
        exact hg ⟨m, k, g, hg', hmn, hinst_m, by simpa using hv⟩
      refine ⟨p, hv, ?_⟩
      rw [lookup_set_ne r n p new hpn]
      exact hlp
  · intro m g hm hinst_m k hk p hvm
    rcases lookup_set_cases hm with ⟨hmn, hg'⟩ | ⟨hmn, hg'⟩
    · subst m; subst g
      rw [hnew] at hinst_m
      unfold Lifecycle.installed at hinst_m
      cases hinst_m
    · have hpn : p ≠ n := by
        intro heq; subst p
        exact hg ⟨m, k, g, hg', hmn, hinst_m, by simpa using hvm⟩
      rcases hwf.viewInstalled m g hg' hinst_m k hk p hvm with ⟨q, hq, hqinst⟩
      refine ⟨q, ?_, hqinst⟩
      rw [lookup_set_ne r n p new hpn]
      exact hq

/-! ## Theorem 59 (Preservation) for the current `Step.next` -/

/-- Every current faithful `Step` preserves full well-formedness of its
registry.  Since `WellFormed` does not inspect table contents, the
table-writing `ψ` half of `Step.next` is harmless; the proof case-splits on
`Step` and applies the `set`/`del` preservation lemmas above. -/
theorem WellFormed.preserved {s : State N K E V} (st : Step s)
    (hwf : WellFormed s.reg) : WellFormed (Step.next st).reg := by
  cases st with
  | oInsert n c p hn hp hdisj =>
      simpa [Step.next, Step.psi, Step.edit] using
        wellFormed_setFreshFull hwf hn rfl rfl hp hdisj rfl
  | oRetire n f hf =>
      let new : Fiber N K V E := { f with retired := true }
      simpa [Step.next, Step.psi, Step.edit, hf, new] using
        wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro h; exact h) (by intro h; exact h)
          (by intro k; rfl)
  | oRemove n f o hf hl hchild =>
      simpa [Step.next, Step.psi, Step.edit] using
        wellFormed_delFull hwf hf hl hchild
  | lBegin n f v hf hl ht htable =>
      simpa [Step.next, Step.psi, Step.edit, hf] using
        wellFormed_lBegin hwf hf hl ht
  | lIter n f ι κ v ι' δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .loading ι' (κ ∘ h) v }
      have hnext_reg :
          (Step.next (Step.lIter n f ι κ v ι' δ h hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf, lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
        (by intro _; rw [hl]; trivial)
        (by intro _; trivial)
        (by intro k; rw [hl]; rfl)
  | lFinish n f ι κ v δ h hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .active (κ ∘ h) v }
      have hnext_reg :
          (Step.next (Step.lFinish n f ι κ v δ h hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf, lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
        (by intro _; rw [hl]; trivial)
        (by intro _; trivial)
        (by intro k; rw [hl]; rfl)
  | lRaise n f ι κ v e hreach hf hl hstep =>
      let new : Fiber N K V E := { f with lc := .unloading κ v (some e) }
      simpa [Step.next, Step.psi, Step.edit, hf] using
        wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
  | lDivertAbort n f ι κ v hreach hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      simpa [Step.next, Step.psi, Step.edit, hf] using
        wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
  | lDivertLand n f ι κ v δ h c hreach hf hl ht hstep =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov δ.2,
                 lc := .unloading (κ ∘ h) v none }
      have hnext_reg :
          (Step.next (Step.lDivertLand n f ι κ v δ h c hreach hf hl ht hstep)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hstep, State.writeEffect_eq_of_lookup hf, lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
        (by intro _; rw [hl]; trivial)
        (by intro _; trivial)
        (by intro k; rw [hl]; rfl)
  | lLeave n f κ v hf hl ht =>
      let new : Fiber N K V E := { f with lc := .unloading κ v none }
      simpa [Step.next, Step.psi, Step.edit, hf] using
        wellFormed_set_viewSame (old := f) (new := new) hwf hf rfl rfl
          (by intro _; rw [hl]; trivial)
          (by intro _; trivial)
          (by intro k; rw [hl]; rfl)
  | lUnload n f κ v o hf hl hg =>
      let new : Fiber N K V E :=
        { f with table := splitTable f.comp.prov (κ (State.fullCtx s)).2,
                 lc := .inactive o }
      have hnext_reg :
          (Step.next (Step.lUnload n f κ v o hf hl hg)).reg =
            set s.reg n new := by
        simp [Step.next, Step.psi, Step.edit, hf, State.writeEffect_eq_of_lookup hf, lookup_set_eq, set_set_eq, new]
      rw [hnext_reg]
      exact wellFormed_lUnload (old := f) (new := new) hwf hf rfl rfl
        (show new.lc = .inactive o by rfl) hg

/-- **Theorem 59 along current `StepTrace`.**  Well-formedness is preserved
by every finite faithful step trace. -/
theorem WellFormed.trace_preserved {s t : State N K E V} (hwf : WellFormed s.reg)
    (ht : StepTrace s t) : WellFormed t.reg := by
  induction ht with
  | nil s => exact hwf
  | @cons s₁ s₂ s₃ st hnext ht ih =>
      exact ih (by
        rw [← hnext]
        exact WellFormed.preserved st hwf)

/-- Same trace preservation, stated under the `StepTrace` namespace. -/
theorem StepTrace.wellFormed_preserved {s t : State N K E V} (ht : StepTrace s t)
    (hwf : WellFormed s.reg) : WellFormed t.reg :=
  WellFormed.trace_preserved hwf ht

end Cordix
