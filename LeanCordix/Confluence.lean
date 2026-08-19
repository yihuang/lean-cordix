import LeanCordix.Trace
import LeanCordix.Progress
import LeanCordix.TableConfined
import LeanCordix.Invariance
import LeanCordix.Equivariance
import LeanCordix.Vestigial

/-!
# LeanCordix.Confluence — Theorem 73 confluence scaffolding

This module ports the confluence part of deleted Theorem 73 onto the current
faithful full-context model.

It provides:

* `Fiber.TotalOnProvision`, `Component.TotalOnProvision`,
  `Registry.TotalOnProvision` (Definition 69);
* `SupportLt` (the relation underlying Definition 67);
* `SupportedBy` (one-step support with a support-set parameter) and
  `Supported` (least fixed point / inductively defined support set);
* `Lemma68Statement`, `Lemma70Statement`, and `Lemma71Statement` as explicit
  propositions recording the paper's lemmas;
* a proved special case of Lemma 71: `O-Remove`/`O-Remove` control edits
  on distinct fibers commute, together with the fact that control-step
  `Ψ` maps are the identity.

The full transposition lemma (including transporting step records across
the swapped states and proving all lifecycle-rule premises) is not yet
formalised; the statement is recorded in `Lemma71Statement`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

noncomputable section
open Classical

/-! ## Definition 69: totality on provision -/

/-- A fiber is *total on its provision* when, if installed, its table is
defined on every key its component provides. -/
def Fiber.TotalOnProvision (f : Fiber N K V E) : Prop :=
  f.lc.installed → ∀ k, k ∈ f.comp.prov → (f.table k).isSome

/-- A component is *total on its provision* when every fiber instantiating
it is total on that component's provision.  This is the component-level
reading of Definition 69 in the current model, where the table lives on the
fiber rather than on the component. -/
def Component.TotalOnProvision (c : Component K V E) : Prop :=
  ∀ f : Fiber N K V E, f.comp = c → Fiber.TotalOnProvision f

/-- Every fiber in a registry is total on its provision. -/
def Registry.TotalOnProvision (r : Registry N K V E) : Prop :=
  ∀ n f, lookup r n = some f → Fiber.TotalOnProvision f

/-! ## Definition 67: support -/

/-- The support relation used in Definition 67: `n` is immediately below
`m` when `n` precedes `m` or `n` is `m`'s parent. -/
def SupportLt (r : Registry N K V E) (n m : N) : Prop :=
  Precedes r n m ∨ ∃ f, lookup r m = some f ∧ f.parent = some n

/-- One step of the support recursion: `n` is supported assuming the set
`S` is already the support set.  The clauses are: not retired, parent (if
any) is supported, and every declared key is provided by a supported
fiber. -/
def SupportedBy (r : Registry N K V E) (S : N → Prop) (n : N) : Prop :=
  ∃ f, lookup r n = some f ∧
    f.retired = false ∧
    (∀ p, f.parent = some p → S p) ∧
    ∀ k, k ∈ f.comp.spec → ∃ m, S m ∧ Precedes r m n

/-- The support set as a least fixed point: `n` is supported when every set
closed under `SupportedBy` contains `n`.  This avoids assuming Lemma 68 and
works even before well-foundedness of `SupportLt` is established. -/
def Supported (r : Registry N K V E) (n : N) : Prop :=
  ∀ S : N → Prop, (∀ m, SupportedBy r S m → S m) → S n

/-- A registry is reachable by a finite step sequence from the empty
registry.  This is the reachability side condition used in Lemma 68. -/
def ReachedFromEmpty (r : Registry N K V E) : Prop :=
  ∃ s t : State N K E V, ∃ ht : StepTrace s t,
    s.reg = ([] : Registry N K V E) ∧ t.reg = r

/-- **Lemma 68 (statement).**  If precedence is acyclic and `r` is reached
by a sequence of steps, then the support relation is well founded. -/
def Lemma68Statement : Prop :=
  ∀ {r : Registry N K V E}, Acyclic r → ReachedFromEmpty r → WellFounded (SupportLt r)

/-- **Lemma 70 (statement).**  Under acyclicity, quiescence, no failed
fibers, and totality on provision, the support set is exactly the set of
active fibers. -/
def Lemma70Statement : Prop :=
  ∀ (s : State N K E V),
    Acyclic s.reg →
    State.quiet s →
    (∀ n f, lookup s.reg n = some f → ¬ f.lc.failed) →
    Registry.TotalOnProvision s.reg →
    ∀ n, Supported s.reg n ↔
      (∃ f, lookup s.reg n = some f ∧ ∃ κ v, f.lc = .active κ v)

/-- **Lemma 71 (statement).**  Two adjacent steps acting on distinct fibers
can be transposed, under iterator independence and the well-formedness
side conditions, to reach the same final state.  The full proof still needs
to transport the second step's record to the swapped intermediate state and
to verify that all lifecycle/control premises survive; this proposition
records the intended conclusion. -/
def Lemma71Statement : Prop :=
  ∀ {s₁ s₂ s₃ : State N K E V} (st₁ : Step s₁) (h₁₂ : Step.next st₁ = s₂)
    (st₂ : Step s₂) (h₂₃ : Step.next st₂ = s₃)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : Iterator.Independent (iterOf st₁.name) (iterOf st₂.name))
    (hiter₁ : ∀ f, lookup s₁.reg st₁.name = some f → iterOf st₁.name = f.comp.iter)
    (hiter₂ : ∀ f, lookup s₂.reg st₂.name = some f → iterOf st₂.name = f.comp.iter)
    (hne : st₁.name ≠ st₂.name)
    (hwf : WellFormed s₁.reg),
    ∃ st₂' : Step s₁, ∃ s₂' : State N K E V,
      Step.next st₂' = s₂' ∧
      ∃ st₁' : Step s₂', Step.next st₁' = s₃

/-! ## A proved special case of Lemma 71

The full transposition proof is large because it must transport `Step`
records across swapped states and re-check premises.  As a useful special
case we prove the control/edit half for `O-Remove`/`O-Remove`: their edits
act on disjoint registry names and therefore commute exactly.  We also prove
that all orchestration (control) steps have identity `Ψ`, so their effect
maps trivially commute. -/

/-- Deleting two distinct names from a registry commutes. -/
theorem del_del_comm (r : Registry N K V E) (n m : N) (h : n ≠ m) :
    del (del r n) m = del (del r m) n := by
  induction r with
  | nil => simp [del]
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · by_cases hpm : p.1 = m
        · exfalso
          exact h (hpn.symm.trans hpm)
        · simp [del, hpn, hpm, h, Ne.symm h, ih]
      · by_cases hpm : p.1 = m
        · simp [del, hpn, hpm, h, Ne.symm h, ih]
        · simp [del, hpn, hpm, h, Ne.symm h, ih]

/-- An orchestration/control kind is one of the three `O-*` rules. -/
def IsControlKind (k : Full.StepKind) : Prop :=
  k = Full.StepKind.oInsert ∨ k = Full.StepKind.oRetire ∨ k = Full.StepKind.oRemove

/-- Control steps have the identity `Ψ` map.  Hence their effect maps
commute trivially with any other step's effect map. -/
theorem psi_eq_id_of_control {s : State N K E V} (st : Step s)
    (h : IsControlKind st.kind) :
    Step.psi st = id := by
  funext x
  cases st with
  | oInsert n c p hn hp hdisj => simp [Step.psi]
  | oRetire n f hf => simp [Step.psi]
  | oRemove n f o hf hl hchild => simp [Step.psi]
  | _ => simp [IsControlKind, Step.kind] at h

/-- The identity `Ψ` maps of two control steps commute as functions. -/
theorem psi_commute_of_control {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : IsControlKind st₁.kind) (h₂ : IsControlKind st₂.kind) :
    Step.psi st₁ ∘ Step.psi st₂ = Step.psi st₂ ∘ Step.psi st₁ := by
  rw [psi_eq_id_of_control st₁ h₁, psi_eq_id_of_control st₂ h₂]

/-- **Lemma 71 special case: `O-Remove`/`O-Remove`.**  The edits of two
`O-Remove` steps acting on distinct names commute exactly on every state.
This is the control/edit half of transposition for the deletion rule. -/
theorem edit_oRemove_oRemove_commute {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : st₁.kind = Full.StepKind.oRemove)
    (h₂ : st₂.kind = Full.StepKind.oRemove)
    (hne : st₁.name ≠ st₂.name) :
    ∀ x : State N K E V, Step.edit st₁ (Step.edit st₂ x) = Step.edit st₂ (Step.edit st₁ x) := by
  intro x
  cases x with
  | mk xreg xamb =>
      cases st₁ with
      | oRemove n₁ f₁ o₁ hf₁ hl₁ hchild₁ =>
          cases st₂ with
          | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
              simp [Step.kind] at h₁ h₂
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              simp [Step.edit, del_del_comm xreg n₁ n₂ hne']
          | _ => simp [Step.kind] at h₂
      | _ => simp [Step.kind] at h₁

/-! ## Additional control-step edit commutations

The following lemmas prove the edit half of Lemma 71 for the remaining
control-step combinations.  `O-Retire` requires the retired fiber to be
present in the state being edited; `O-Insert` requires its name to be fresh
in that state.  These are the minimal side conditions needed for exact
state equality with the current list-based registry. -/

/-- Updating two distinct names that are both present in a registry
commutes. -/
theorem set_set_comm_of_lookup {r : Registry N K V E} {n m : N}
    {f g : Fiber N K V E} (hne : n ≠ m)
    (hn : ∃ f', lookup r n = some f') (hm : ∃ g', lookup r m = some g') :
    set (set r n f) m g = set (set r m g) n f := by
  induction r with
  | nil =>
      rcases hn with ⟨f', hf'⟩
      cases hf'
  | cons p rest ih =>
      rcases hn with ⟨fn, hfn⟩
      rcases hm with ⟨gm, hgm⟩
      by_cases hpn : p.1 = n
      · by_cases hpm : p.1 = m
        · exfalso
          exact hne (hpn.symm.trans hpm)
        · simp [set, hpn, hpm]
          have hm' : ∃ g', lookup rest m = some g' := by
            exact ⟨gm, by simpa [lookup, hpm] using hgm⟩
          simp [set, hpn, hpm, hne, Ne.symm hne]
      · by_cases hpm : p.1 = m
        · simp [set, hpn, hpm]
          have hn' : ∃ f', lookup rest n = some f' := by
            exact ⟨fn, by simpa [lookup, hpn] using hfn⟩
          simp [set, hpn, hpm, hne, Ne.symm hne]
        · simp [set, hpn, hpm]
          have hn' : ∃ f', lookup rest n = some f' := by
            exact ⟨fn, by simpa [lookup, hpn] using hfn⟩
          have hm' : ∃ g', lookup rest m = some g' := by
            exact ⟨gm, by simpa [lookup, hpm] using hgm⟩
          rw [ih hn' hm']

/-- Setting a present name and deleting a distinct name commute. -/
theorem set_del_comm_of_lookup {r : Registry N K V E} {n m : N}
    {f : Fiber N K V E} (hne : n ≠ m)
    (hm : ∃ g, lookup r m = some g) :
    del (set r m f) n = set (del r n) m f := by
  induction r with
  | nil =>
      rcases hm with ⟨g, hg⟩
      cases hg
  | cons p rest ih =>
      rcases hm with ⟨gm, hgm⟩
      by_cases hpm : p.1 = m
      · by_cases hpn : p.1 = n
        · exfalso
          exact hne (hpn.symm.trans hpm)
        · simp [set, del, hpm, hpn, hne, Ne.symm hne]
      · by_cases hpn : p.1 = n
        · simp [set, del, hpm, hpn, hne, Ne.symm hne]
          have hm' : ∃ g, lookup rest m = some g := by
            exact ⟨gm, by simpa [lookup, hpm] using hgm⟩
          rw [ih hm']
        · simp [set, del, hpm, hpn, hne, Ne.symm hne]
          have hm' : ∃ g, lookup rest m = some g := by
            exact ⟨gm, by simpa [lookup, hpm] using hgm⟩
          rw [ih hm']

/-- Inserting a fresh name and updating a present distinct name commute. -/
theorem set_set_comm_of_fresh_present {r : Registry N K V E} {n m : N}
    {f g : Fiber N K V E} (hne : n ≠ m)
    (hn : lookup r n = none) (hm : ∃ g0, lookup r m = some g0) :
    set (set r m g) n f = set (set r n f) m g := by
  induction r with
  | nil =>
      rcases hm with ⟨g0, hg0⟩
      cases hg0
  | cons p rest ih =>
      rcases hm with ⟨g0, hg0⟩
      by_cases hpn : p.1 = n
      · exfalso
        simp [lookup, hpn] at hn
      · by_cases hpm : p.1 = m
        · simp [set, hpn, hpm, hne, Ne.symm hne]
        · simp [set, hpn, hpm]
          have hn' : lookup rest n = none := by
            simpa [lookup, hpn] using hn
          have hm' : ∃ g0, lookup rest m = some g0 := by
            exact ⟨g0, by simpa [lookup, hpm] using hg0⟩
          rw [ih hn' hm']

/-- Inserting a fresh name and deleting a distinct name commute. -/
theorem set_del_comm_of_fresh {r : Registry N K V E} {n m : N}
    {f : Fiber N K V E} (hne : n ≠ m)
    (hn : lookup r n = none) :
    del (set r n f) m = set (del r m) n f := by
  induction r with
  | nil => simp [set, del, hne, Ne.symm hne]
  | cons p rest ih =>
      by_cases hpn : p.1 = n
      · exfalso
        simp [lookup, hpn] at hn
      · by_cases hpm : p.1 = m
        · simp [set, del, hpn, hpm, hne, Ne.symm hne]
          have hn' : lookup rest n = none := by
            simpa [lookup, hpn] using hn
          rw [ih hn']
        · simp [set, del, hpn, hpm]
          have hn' : lookup rest n = none := by
            simpa [lookup, hpn] using hn
          rw [ih hn']

/-- **Lemma 71 special case: `O-Retire`/`O-Retire`.**  The edits of two
`O-Retire` steps on distinct names commute when both names are present in
the edited state. -/
theorem edit_oRetire_oRetire_commute {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : st₁.kind = Full.StepKind.oRetire)
    (h₂ : st₂.kind = Full.StepKind.oRetire)
    (hne : st₁.name ≠ st₂.name) :
    ∀ x : State N K E V,
      (∃ g₁, lookup x.reg st₁.name = some g₁) →
      (∃ g₂, lookup x.reg st₂.name = some g₂) →
      Step.edit st₁ (Step.edit st₂ x) = Step.edit st₂ (Step.edit st₁ x) := by
  intro x hx₁ hx₂
  cases x with
  | mk xreg xamb =>
      rcases hx₁ with ⟨g₁, hg₁⟩
      rcases hx₂ with ⟨g₂, hg₂⟩
      cases st₁ with
      | oRetire n₁ f₁ hf₁ =>
          cases st₂ with
          | oRetire n₂ f₂ hf₂ =>
              simp [Step.kind] at h₁ h₂
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              have hx₁' : lookup xreg n₁ = some g₁ := by simpa [Step.name] using hg₁
              have hx₂' : lookup xreg n₂ = some g₂ := by simpa [Step.name] using hg₂
              simp [Step.edit, hx₁', hx₂', lookup_set_ne, hne', Ne.symm hne',
                set_set_comm_of_lookup (r := xreg) (n := n₁) (m := n₂)
                  (f := { g₁ with retired := true }) (g := { g₂ with retired := true })
                  hne' ⟨g₁, hx₁'⟩ ⟨g₂, hx₂'⟩]
          | _ => simp [Step.kind] at h₂
      | _ => simp [Step.kind] at h₁

/-- **Lemma 71 special case: `O-Retire`/`O-Remove`.**  The edits of an
`O-Retire` and an `O-Remove` on distinct names commute when the retired
name is present in the edited state. -/
theorem edit_oRetire_oRemove_commute {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : st₁.kind = Full.StepKind.oRetire)
    (h₂ : st₂.kind = Full.StepKind.oRemove)
    (hne : st₁.name ≠ st₂.name) :
    ∀ x : State N K E V,
      (∃ g, lookup x.reg st₁.name = some g) →
      Step.edit st₁ (Step.edit st₂ x) = Step.edit st₂ (Step.edit st₁ x) := by
  intro x hx₁
  cases x with
  | mk xreg xamb =>
      rcases hx₁ with ⟨g₁, hg₁⟩
      cases st₁ with
      | oRetire n₁ f₁ hf₁ =>
          cases st₂ with
          | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
              simp [Step.kind] at h₁ h₂
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              have hx₁' : lookup xreg n₁ = some g₁ := by simpa [Step.name] using hg₁
              simp [Step.edit, hx₁', del, lookup_del_ne, hne',
                set_del_comm_of_lookup (r := xreg) (n := n₂) (m := n₁)
                  (f := { g₁ with retired := true }) (Ne.symm hne') ⟨g₁, hx₁'⟩]
          | _ => simp [Step.kind] at h₂
      | _ => simp [Step.kind] at h₁

/-- **Lemma 71 special case: `O-Insert`/`O-Retire`.**  The edits of an
`O-Insert` at a fresh name and an `O-Retire` on a distinct name commute. -/
theorem edit_oInsert_oRetire_commute {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : st₁.kind = Full.StepKind.oInsert)
    (h₂ : st₂.kind = Full.StepKind.oRetire)
    (hne : st₁.name ≠ st₂.name) :
    ∀ x : State N K E V,
      lookup x.reg st₁.name = none →
      Step.edit st₁ (Step.edit st₂ x) = Step.edit st₂ (Step.edit st₁ x) := by
  intro x hfresh
  cases x with
  | mk xreg xamb =>
      cases st₁ with
      | oInsert n₁ c₁ p₁ hn₁ hp₁ hdisj₁ =>
          cases st₂ with
          | oRetire n₂ f₂ hf₂ =>
              simp [Step.kind] at h₁ h₂
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              have hfresh' : lookup xreg n₁ = none := by simpa [Step.name] using hfresh
              by_cases h₂some : (lookup xreg n₂).isSome
              · rcases Option.isSome_iff_exists.mp h₂some with ⟨g₂, hg₂⟩
                simp [Step.edit, hfresh', hg₂, lookup_set_ne, Ne.symm hne',
                  set_set_comm_of_fresh_present (r := xreg) (n := n₁) (m := n₂)
                    (f := { comp := c₁, parent := p₁, table := fun _ => none, retired := false, lc := Lifecycle.inactive none })
                    (g := { g₂ with retired := true })
                    hne' hfresh' ⟨g₂, hg₂⟩]
              · have hn₂ : lookup xreg n₂ = none := Option.not_isSome_iff_eq_none.mp h₂some
                simp [Step.edit, hfresh', hn₂, lookup_set_ne, Ne.symm hne']
          | _ => simp [Step.kind] at h₂
      | _ => simp [Step.kind] at h₁

/-- **Lemma 71 special case: `O-Insert`/`O-Remove`.**  The edits of an
`O-Insert` at a fresh name and an `O-Remove` on a distinct name commute. -/
theorem edit_oInsert_oRemove_commute {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : st₁.kind = Full.StepKind.oInsert)
    (h₂ : st₂.kind = Full.StepKind.oRemove)
    (hne : st₁.name ≠ st₂.name) :
    ∀ x : State N K E V,
      lookup x.reg st₁.name = none →
      Step.edit st₁ (Step.edit st₂ x) = Step.edit st₂ (Step.edit st₁ x) := by
  intro x hfresh
  cases x with
  | mk xreg xamb =>
      cases st₁ with
      | oInsert n₁ c₁ p₁ hn₁ hp₁ hdisj₁ =>
          cases st₂ with
          | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
              simp [Step.kind] at h₁ h₂
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              have hfresh' : lookup xreg n₁ = none := by simpa [Step.name] using hfresh
              simp [Step.edit, hfresh', del, lookup_del_ne, hne',
                set_del_comm_of_fresh (r := xreg) (n := n₁) (m := n₂)
                  (f := { comp := c₁, parent := p₁, table := fun _ => none, retired := false, lc := Lifecycle.inactive none })
                  hne' hfresh']
          | _ => simp [Step.kind] at h₂
      | _ => simp [Step.kind] at h₁

/-- **Lemma 71 control-step special case.**  For two control steps on
distinct names, the edit composition (hence the `next` composition, since
control `Ψ` maps are identity) is independent of order.  The side conditions
are the minimal ones needed by the individual control edit lemmas:
at most one `O-Insert`, `O-Retire` names must be present, and `O-Insert`
names must be fresh. -/
theorem next_commute_of_control_distinct {s : State N K E V} (st₁ st₂ : Step s)
    (h₁ : IsControlKind st₁.kind) (h₂ : IsControlKind st₂.kind)
    (hne : st₁.name ≠ st₂.name)
    (hno_insert_insert : ¬ (st₁.kind = Full.StepKind.oInsert ∧ st₂.kind = Full.StepKind.oInsert))
    (hret₁ : st₁.kind = Full.StepKind.oRetire → ∃ g, lookup s.reg st₁.name = some g)
    (hret₂ : st₂.kind = Full.StepKind.oRetire → ∃ g, lookup s.reg st₂.name = some g)
    (hins₁ : st₁.kind = Full.StepKind.oInsert → lookup s.reg st₁.name = none)
    (hins₂ : st₂.kind = Full.StepKind.oInsert → lookup s.reg st₂.name = none) :
    Step.edit st₁ (Step.edit st₂ s) = Step.edit st₂ (Step.edit st₁ s) := by
  cases st₁ with
  | oInsert n₁ c₁ p₁ hn₁ hp₁ hdisj₁ =>
      cases st₂ with
      | oInsert n₂ c₂ p₂ hn₂ hp₂ hdisj₂ =>
          exfalso
          exact hno_insert_insert ⟨rfl, rfl⟩
      | oRetire n₂ f₂ hf₂ =>
          exact edit_oInsert_oRetire_commute
            (Step.oInsert n₁ c₁ p₁ hn₁ hp₁ hdisj₁) (Step.oRetire n₂ f₂ hf₂)
            (by simp [Step.kind]) (by simp [Step.kind]) hne s (hins₁ rfl)
      | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
          exact edit_oInsert_oRemove_commute
            (Step.oInsert n₁ c₁ p₁ hn₁ hp₁ hdisj₁) (Step.oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂)
            (by simp [Step.kind]) (by simp [Step.kind]) hne s (hins₁ rfl)
      | _ => simp [IsControlKind, Step.kind] at h₂
  | oRetire n₁ f₁ hf₁ =>
      cases st₂ with
      | oInsert n₂ c₂ p₂ hn₂ hp₂ hdisj₂ =>
          exact (edit_oInsert_oRetire_commute
            (Step.oInsert n₂ c₂ p₂ hn₂ hp₂ hdisj₂) (Step.oRetire n₁ f₁ hf₁)
            (by simp [Step.kind]) (by simp [Step.kind]) (Ne.symm hne) s (hins₂ rfl)).symm
      | oRetire n₂ f₂ hf₂ =>
          exact edit_oRetire_oRetire_commute
            (Step.oRetire n₁ f₁ hf₁) (Step.oRetire n₂ f₂ hf₂)
            (by simp [Step.kind]) (by simp [Step.kind]) hne s (hret₁ rfl) (hret₂ rfl)
      | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
          exact edit_oRetire_oRemove_commute
            (Step.oRetire n₁ f₁ hf₁) (Step.oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂)
            (by simp [Step.kind]) (by simp [Step.kind]) hne s (hret₁ rfl)
      | _ => simp [IsControlKind, Step.kind] at h₂
  | oRemove n₁ f₁ o₁ hf₁ hl₁ hchild₁ =>
      cases st₂ with
      | oInsert n₂ c₂ p₂ hn₂ hp₂ hdisj₂ =>
          exact (edit_oInsert_oRemove_commute
            (Step.oInsert n₂ c₂ p₂ hn₂ hp₂ hdisj₂) (Step.oRemove n₁ f₁ o₁ hf₁ hl₁ hchild₁)
            (by simp [Step.kind]) (by simp [Step.kind]) (Ne.symm hne) s (hins₂ rfl)).symm
      | oRetire n₂ f₂ hf₂ =>
          exact (edit_oRetire_oRemove_commute
            (Step.oRetire n₂ f₂ hf₂) (Step.oRemove n₁ f₁ o₁ hf₁ hl₁ hchild₁)
            (by simp [Step.kind]) (by simp [Step.kind]) (Ne.symm hne) s (hret₂ rfl)).symm
      | oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂ =>
          exact edit_oRemove_oRemove_commute
            (Step.oRemove n₁ f₁ o₁ hf₁ hl₁ hchild₁) (Step.oRemove n₂ f₂ o₂ hf₂ hl₂ hchild₂)
            (by simp [Step.kind]) (by simp [Step.kind]) hne s
      | _ => simp [IsControlKind, Step.kind] at h₂
  | _ => simp [IsControlKind, Step.kind] at h₁

/-- **Lemma 71 special case: `L-Begin`/`L-Begin`.**  Two `L-Begin` steps on
distinct names commute exactly.  `L-Begin` has identity `Ψ`, so this is the
corresponding edit commutation; it holds without extra side conditions
because an absent name makes the `L-Begin` edit the identity. -/
theorem next_commute_of_lBegin_lBegin_distinct {s : State N K E V} (st1 st2 : Step s)
    (h1 : st1.kind = Full.StepKind.lBegin)
    (h2 : st2.kind = Full.StepKind.lBegin)
    (hne : st1.name ≠ st2.name) :
    Step.edit st1 (Step.edit st2 s) = Step.edit st2 (Step.edit st1 s) := by
  cases s with
  | mk sreg samb =>
      cases st1 with
      | lBegin n₁ f₁ v₁ hf₁ hl₁ ht₁ htable₁ =>
          cases st2 with
          | lBegin n₂ f₂ v₂ hf₂ hl₂ ht₂ htable₂ =>
              simp [Step.kind] at h1 h2
              have hne' : n₁ ≠ n₂ := by
                simpa [Step.name] using hne
              by_cases h₁some : (lookup sreg n₁).isSome
              · rcases Option.isSome_iff_exists.mp h₁some with ⟨g₁, hg₁⟩
                by_cases h₂some : (lookup sreg n₂).isSome
                · rcases Option.isSome_iff_exists.mp h₂some with ⟨g₂, hg₂⟩
                  simp [Step.edit, hg₁, hg₂, lookup_set_ne, hne', Ne.symm hne',
                    set_set_comm_of_lookup (r := sreg) (n := n₁) (m := n₂)
                      (f := { g₁ with lc := .loading g₁.comp.iter id v₁ })
                      (g := { g₂ with lc := .loading g₂.comp.iter id v₂ })
                      hne' ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩]
                · have hn₂ : lookup sreg n₂ = none := Option.not_isSome_iff_eq_none.mp h₂some
                  simp [Step.edit, hg₁, hn₂, lookup_set_ne, hne', Ne.symm hne']
              · have hn₁ : lookup sreg n₁ = none := Option.not_isSome_iff_eq_none.mp h₁some
                by_cases h₂some : (lookup sreg n₂).isSome
                · rcases Option.isSome_iff_exists.mp h₂some with ⟨g₂, hg₂⟩
                  simp [Step.edit, hn₁, hg₂, lookup_set_ne, hne', Ne.symm hne']
                · have hn₂ : lookup sreg n₂ = none := Option.not_isSome_iff_eq_none.mp h₂some
                  simp [Step.edit, hn₁, hn₂]
          | _ => simp [Step.kind] at h2
      | _ => simp [Step.kind] at h1

end -- noncomputable section

end Cordix
