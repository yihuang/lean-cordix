import LeanCordix.TraceModel

/-
# Cordix — Lemma 55 support: observational state equivalence

This module defines the observational equivalence relation used by
Lemma 55 (`≃`-invariance).  A lifecycle state is related to another when the
rule-visible fields are equal, with iterators compared by their complete
step functions; a state is related when ambient context, `sigmaOf`,
`providerOf`, `targetOf`, `relied`, name domains, and the rule-visible fiber
fields are all equal.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Cordix

namespace Full

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

def Lifecycle.Equiv : Lifecycle N K V E → Lifecycle N K V E → Prop
  | .inactive o, .inactive o' => o = o'
  | .loading ι κ v, .loading ι' κ' v' =>
      (∀ γ, Cordix.Iterator.step ι γ = Cordix.Iterator.step ι' γ) ∧ κ = κ' ∧ v = v'
  | .active κ v, .active κ' v' => κ = κ' ∧ v = v'
  | .unloading κ v o, .unloading κ' v' o' => κ = κ' ∧ v = v' ∧ o = o'
  | _, _ => False

namespace Lifecycle.Equiv

theorem installed_iff {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    lc.installed ↔ lc'.installed := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv, Lifecycle.installed] at h ⊢

theorem viewOf_eq {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    lc.viewOf = lc'.viewOf := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv, Lifecycle.viewOf] at h ⊢
  · rcases h with ⟨_, hκ, hv⟩; exact hv
  · rcases h with ⟨hκ, hv⟩; exact hv
  · rcases h with ⟨hκ, hv, _⟩; exact hv

theorem symm {lc lc' : Lifecycle N K V E} (h : Lifecycle.Equiv lc lc') :
    Lifecycle.Equiv lc' lc := by
  cases lc <;> cases lc' <;> simp [Lifecycle.Equiv] at h ⊢
  · exact h.symm
  · rcases h with ⟨hstep, hκ, hv⟩
    exact ⟨fun γ => (hstep γ).symm, hκ.symm, hv.symm⟩
  · rcases h with ⟨hκ, hv⟩; exact ⟨hκ.symm, hv.symm⟩
  · rcases h with ⟨hκ, hv, ho⟩; exact ⟨hκ.symm, hv.symm, ho.symm⟩

end Lifecycle.Equiv

/-- Observational equivalence of states for the rules of Section 4.3. -/
def State.Equiv (s s' : State N K E V) : Prop :=
  s.ambient = s'.ambient ∧
  Full.sigmaOf s.reg = Full.sigmaOf s'.reg ∧
  Full.providerOf s.reg = Full.providerOf s'.reg ∧
  (∀ n, Full.targetOf s.reg n = Full.targetOf s'.reg n) ∧
  (∀ n, Full.relied s.reg n ↔ Full.relied s'.reg n) ∧
  (∀ n, (lookup s.reg n).isSome ↔ (lookup s'.reg n).isSome) ∧
  ∀ n f f', lookup s.reg n = some f → lookup s'.reg n = some f' →
    f.comp = f'.comp ∧ f.parent = f'.parent ∧ f.retired = f'.retired ∧
      f.table = f'.table ∧ Lifecycle.Equiv f.lc f'.lc

namespace State.Equiv

theorem symm {s s' : State N K E V} (h : State.Equiv s s') : State.Equiv s' s := by
  rcases h with ⟨ha, hsig, hprov, htgt, hrel, hdom, hfields_all⟩
  constructor
  · exact ha.symm
  constructor
  · exact hsig.symm
  constructor
  · exact hprov.symm
  constructor
  · intro n; exact (htgt n).symm
  constructor
  · intro n; exact (hrel n).symm
  constructor
  · intro n; exact (hdom n).symm
  · intro n f' f hf' hf
    have hfields := hfields_all n f f' hf hf'
    exact ⟨hfields.1.symm, hfields.2.1.symm, hfields.2.2.1.symm, hfields.2.2.2.1.symm, Lifecycle.Equiv.symm hfields.2.2.2.2⟩

end State.Equiv

end Full

end Cordix
