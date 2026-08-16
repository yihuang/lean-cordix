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

end Rename

end Full

end Cordix
