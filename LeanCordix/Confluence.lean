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

end -- noncomputable section

end Cordix
