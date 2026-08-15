/-!
# Cordix — Section 3.1: Revertible Effects

This module formalizes Section 3.1 of *A Programming Paradigm for Spatiotemporal
Composability* (Cordix/Cordis): revertible effects, in which every context
transformation carries an inverse that the runtime tracks.

Formalized content:
* Definition 1  — the twisted composition monoid `𝒯_Γ`.
* Definition 2  — the effect context `E_Γ = Γ × (Γ → Γ)`.
* Definition 3  — `track`.
* Theorem 4     — `track` commutes with the state projection.
* Theorem 5     — `track` is a monoid homomorphism.
* Definition 6  — `recover`.
* Theorem 7     — tracking preserves recovery.
* Definition 8  — effect functions `E_Γ` and witnessed effect functions `E*_Γ`.
* Definition 9  — effect composition `⋄`.
* Theorem 10    — `⋄` is a monoid; the pair embedding is a homomorphism.
* Theorem 11    — witnessing survives `⋄`.
* Definition 12 — the lift `effect`.
* Theorem 13    — `effect` preserves `⋄`.
* Theorem 14    — the lift agrees with the lifted map on states.
* Theorem 15    — the lifted inverse recovers the state exactly.
* Theorem 16    — LIFO reversion along a sequence.
* Definition 17 — transformation monoids.
* Lemma 18      — generated monoid closure properties.
* Definition 19 — independence of effect functions.

## A note on composition order

The paper writes function composition so that "the left operand acts after
the right".  We use the standard Lean convention `(f ∘ g) x = f (g x)`
throughout.  With that convention the internally consistent reading of
Section 3.1 (the one under which the proofs of Theorems 5, 7, 13 and 15 go
through) is:

* `track (f, g) (γ, κ) = (f γ, κ ∘ g)`  — the accumulator applies the most
  recently tracked inverse first (LIFO);
* twisted composition `(f₁, g₁) ∘ᵗ (f₂, g₂) = (f₁ ∘ f₂, g₂ ∘ g₁)`;
* effect composition `τ₁ ⋄ τ₂` runs `τ₂` first and yields the composite
  inverse `g ∘ h` (`g` yielded by `τ₂`, `h` by `τ₁`), which again applies
  the last effect's inverse first.
-/

namespace Cordix

universe u

variable {Γ : Type u}

/-! ## Definition 1: the twisted composition monoid -/

/-- `TransPair Γ` is the carrier `(Γ → Γ) × (Γ → Γ)` of the twisted
composition monoid `𝒯_Γ`: pairs of a forward transformation and a candidate
(left) inverse. -/
abbrev TransPair (Γ : Type u) : Type u := (Γ → Γ) × (Γ → Γ)

/-- **Definition 1.** Twisted composition of pairs of context transformations:
the left operand acts after the right, and the inverses accumulate in the
opposite order. -/
def twistedComp (p₁ p₂ : TransPair Γ) : TransPair Γ := (p₁.1 ∘ p₂.1, p₂.2 ∘ p₁.2)

/-- Infix notation for twisted composition. -/
infixr:80 " ∘ᵗ " => twistedComp

/-- The unit `(id, id)` of the twisted composition monoid. -/
def twistedId : TransPair Γ := (id, id)

theorem twistedComp_assoc (p₁ p₂ p₃ : TransPair Γ) :
    (p₁ ∘ᵗ p₂) ∘ᵗ p₃ = p₁ ∘ᵗ (p₂ ∘ᵗ p₃) := by
  refine Prod.ext ?_ ?_ <;> funext γ <;> simp [twistedComp, Function.comp]

theorem twistedComp_id_left (p : TransPair Γ) : twistedId ∘ᵗ p = p := by
  refine Prod.ext ?_ ?_ <;> funext γ <;> simp [twistedComp, twistedId]

theorem twistedComp_id_right (p : TransPair Γ) : p ∘ᵗ twistedId = p := by
  refine Prod.ext ?_ ?_ <;> funext γ <;> simp [twistedComp, twistedId]

/-! ## Definition 2: the effect context -/

/-- **Definition 2.** The effect context `E_Γ = Γ × (Γ → Γ)`: the current
context state together with the accumulator, the composite of the inverses of
the effects performed so far. -/
abbrev EffectCtx (Γ : Type u) : Type u := Γ × (Γ → Γ)

namespace EffectCtx

/-- `pr₁`: the current context state. -/
abbrev cur {Γ : Type u} (ec : EffectCtx Γ) : Γ := ec.1

/-- `pr₂`: the accumulator. -/
abbrev acc {Γ : Type u} (ec : EffectCtx Γ) : Γ → Γ := ec.2

end EffectCtx

/-! ## Definitions 3 and 6: track and recover -/

/-- **Definition 3.** `track (f, g)` transforms the state by `f` and composes
the inverse `g` onto the accumulator.  The accumulator applies the most
recently tracked inverse first, so a sequence of tracks recovers in LIFO
order. -/
def track (p : TransPair Γ) : EffectCtx Γ → EffectCtx Γ :=
  fun ec => (p.1 ec.1, ec.2 ∘ p.2)

/-- **Definition 6.** `recover` applies the accumulator to the current state
and resets it to the identity. -/
def recover {Γ : Type u} : EffectCtx Γ → EffectCtx Γ :=
  fun ec => (ec.2 ec.1, id)

/-- **Theorem 4.** Tracking commutes with the state projection:
`pr₁ ∘ track (f, g) = f ∘ pr₁`. -/
theorem cur_track (p : TransPair Γ) (ec : EffectCtx Γ) :
    (track p ec).cur = p.1 ec.cur := rfl

/-- **Theorem 5 (part 1).** `track` carries the unit to the identity. -/
theorem track_id : (track twistedId : EffectCtx Γ → EffectCtx Γ) = id := by
  funext ec
  refine Prod.ext (by simp [track, twistedId]) ?_
  funext γ
  simp [track, twistedId]

/-- **Theorem 5 (part 2).** `track` is a monoid homomorphism from the twisted
composition monoid into `E_Γ → E_Γ`. -/
theorem track_comp (p₁ p₂ : TransPair Γ) :
    track (p₁ ∘ᵗ p₂) = track p₁ ∘ track p₂ := by
  funext ec
  refine Prod.ext (by simp [track, twistedComp, Function.comp]) ?_
  funext γ
  simp [track, twistedComp, Function.comp]

/-- **Theorem 7.** Tracking preserves recovery: if `g` reverts `f` at the
current state, then recovering after tracking agrees with recovering before. -/
theorem recover_track {f g : Γ → Γ} {ec : EffectCtx Γ} (h : g (f ec.cur) = ec.cur) :
    recover (track (f, g) ec) = recover ec := by
  simp only [track, recover, Function.comp]
  rw [h]

/-! ## Definitions 8–9: effect functions and their composition -/

/-- **Definition 8.** An effect function `τ : E_Γ` transforms the context and
returns, alongside the new context, the inverse of the effect *at the state
where it was applied*. -/
abbrev Eff (Γ : Type u) : Type u := Γ → Γ × (Γ → Γ)

/-- The unit effect function `η_Γ = γ ↦ (γ, id)`. -/
def effId : Eff Γ := fun γ => (γ, id)

/-- **Definition 9.** Effect composition `⋄`: `τ₂` runs first, and the
composite inverse is `g ∘ h` with `g` yielded by `τ₂` and `h` by `τ₁` — the
last effect's inverse applies first (LIFO). -/
def effComp (τ₁ τ₂ : Eff Γ) : Eff Γ :=
  fun γ => ((τ₁ ((τ₂ γ).1)).1, (τ₂ γ).2 ∘ (τ₁ ((τ₂ γ).1)).2)

/-- Infix notation for effect composition. -/
infixr:80 " ⋄ " => effComp

/-- The forward map `pr₁ ∘ τ` of an effect function. -/
def fwd (τ : Eff Γ) : Γ → Γ := fun γ => (τ γ).1

/-- **Definition 8.** `τ` is *witnessed* (`τ ∈ E*_Γ`) when the inverse it
yields at each state reverts the effect at that state. -/
def Witnessed (τ : Eff Γ) : Prop := ∀ γ, (τ γ).2 ((τ γ).1) = γ

/-- **Theorem 10 (part 1).** `(E_Γ, ⋄, η_Γ)` is a monoid. -/
theorem effComp_assoc (τ₁ τ₂ τ₃ : Eff Γ) : (τ₁ ⋄ τ₂) ⋄ τ₃ = τ₁ ⋄ (τ₂ ⋄ τ₃) := by
  funext γ
  refine Prod.ext rfl ?_
  funext x
  simp [effComp, Function.comp]

theorem effComp_id_left (τ : Eff Γ) : effId ⋄ τ = τ := by
  funext γ
  refine Prod.ext rfl ?_
  funext x
  simp [effComp, effId]

theorem effComp_id_right (τ : Eff Γ) : τ ⋄ effId = τ := by
  funext γ
  exact Prod.ext rfl (by funext x; simp [effComp, effId])

/-- The monoid homomorphism of Theorem 10 (part 2): a pair of transformations
with a uniform inverse induces an effect function. -/
def pairToEff (p : TransPair Γ) : Eff Γ := fun γ => (p.1 γ, p.2)

/-- **Theorem 10 (part 2).** The assignment `(f, g) ↦ (γ ↦ (f γ, g))` is a
monoid homomorphism from `𝒯_Γ` into `E_Γ`. -/
theorem pairToEff_comp (p₁ p₂ : TransPair Γ) :
    pairToEff (p₁ ∘ᵗ p₂) = pairToEff p₁ ⋄ pairToEff p₂ := by
  funext γ
  exact Prod.ext rfl (by funext x; simp [effComp, pairToEff, twistedComp, Function.comp])

/-- **Theorem 11 (part 1).** `E*_Γ` is a submonoid of `E_Γ`: the unit is
witnessed and witnessing is closed under `⋄`. -/
theorem witnessed_effId : Witnessed (effId : Eff Γ) := fun _ => rfl

theorem witnessed_effComp {τ₁ τ₂ : Eff Γ} (h₁ : Witnessed τ₁) (h₂ : Witnessed τ₂) :
    Witnessed (τ₁ ⋄ τ₂) := by
  intro γ
  have e₂ : (τ₂ γ).2 ((τ₂ γ).1) = γ := h₂ γ
  have e₁ : (τ₁ ((τ₂ γ).1)).2 ((τ₁ ((τ₂ γ).1)).1) = (τ₂ γ).1 := h₁ ((τ₂ γ).1)
  show ((τ₂ γ).2 ∘ (τ₁ ((τ₂ γ).1)).2) ((τ₁ ((τ₂ γ).1)).1) = γ
  simp only [Function.comp_apply, e₁]
  exact e₂

/-- **Theorem 11 (part 2).** A uniform inverse (`g` reverting `f` at every
state) witnesses at every state. -/
theorem witnessed_pairToEff {f g : Γ → Γ} (h : ∀ γ, g (f γ) = γ) :
    Witnessed (pairToEff (f, g)) := fun γ => h γ

/-! ## Definition 12: the lift `effect` -/

/-- **Definition 12.** `effect τ` lifts an effect function to the effect
context: the accumulator is extended with the freshly yielded inverse, and the
inverse it returns is `track (g, pr₁ ∘ τ)` — undoing the effect is performed
by `g`, and the way to undo *that* is to perform the effect again. -/
def effectLift (τ : Eff Γ) : Eff (EffectCtx Γ) :=
  fun ec => (((τ ec.1).1, ec.2 ∘ (τ ec.1).2), track ((τ ec.1).2, fwd τ))

theorem fwd_comp (τ₁ τ₂ : Eff Γ) : fwd (τ₁ ⋄ τ₂) = fwd τ₁ ∘ fwd τ₂ := by
  funext γ
  rfl

/-- **Theorem 13.** `effect` preserves `⋄`. -/
theorem effectLift_comp (τ₁ τ₂ : Eff Γ) :
    effectLift (τ₁ ⋄ τ₂) = effectLift τ₁ ⋄ effectLift τ₂ := by
  funext ec
  refine Prod.ext rfl ?_
  funext ec₂
  rfl

/-- **Theorem 14 (part 1).** The lift agrees with the lifted map on states:
`pr₁ ∘ pr₁ ∘ effect τ = (pr₁ ∘ τ) ∘ pr₁`. -/
theorem cur_effectLift (τ : Eff Γ) (ec : EffectCtx Γ) :
    ((effectLift τ ec).1).cur = fwd τ ec.cur := rfl

/-- **Theorem 14 (part 2).** The lifted inverse agrees with the lifted
inverse on states (Theorem 4 applied to the swapped pair). -/
theorem cur_invLift (τ : Eff Γ) (ec : EffectCtx Γ) :
    ((effectLift τ ec).2 ec).cur = (τ ec.cur).2 ec.cur :=
  cur_track _ _

/-- The soundness invariant of a state: `κ γ` is the recovery target. -/
def soundness (ec : EffectCtx Γ) : Γ := ec.2 ec.1

theorem soundness_track {f g : Γ → Γ} {ec : EffectCtx Γ} (h : g (f ec.cur) = ec.cur) :
    soundness (track (f, g) ec) = soundness ec := by
  simp [soundness, track, Function.comp, h]

theorem soundness_effectLift (τ : Eff Γ) (w : Witnessed τ) (ec : EffectCtx Γ) :
    soundness ((effectLift τ ec).1) = soundness ec := by
  have hw : (τ ec.1).2 ((τ ec.1).1) = ec.1 := w ec.1
  simp [soundness, effectLift, Function.comp, hw]

/-- **Theorem 15.** Let `τ ∈ E*_Γ`, fix `ec = (γ, κ) ∈ E_Γ`, and write
`(Δ, ν) = effect τ ec`.  Then `ν Δ = (γ, κ ∘ g ∘ fwd τ)`: the state is
recovered exactly, the accumulator is restored iff `g ∘ fwd τ = id`, and in
every case the soundness invariant `κ γ` is preserved. -/
theorem invLift_apply (τ : Eff Γ) (w : Witnessed τ) (ec : EffectCtx Γ) :
    (effectLift τ ec).2 ((effectLift τ ec).1) = (ec.cur, ec.2 ∘ (τ ec.cur).2 ∘ fwd τ) := by
  have hw : (τ ec.1).2 ((τ ec.1).1) = ec.1 := w ec.1
  show (track ((τ ec.1).2, fwd τ) ((τ ec.1).1, ec.2 ∘ (τ ec.1).2)) = _
  simp only [track]
  exact Prod.ext hw rfl

/-- **Theorem 15 (corollary).** The lift is itself witnessed exactly when
`τ` is witnessed and its yielded inverse reverts `τ`'s forward map
*everywhere* (not merely at the state of application). -/
theorem witnessed_effectLift_iff (τ : Eff Γ) :
    Witnessed (effectLift τ) ↔ Witnessed τ ∧ ∀ γ, ((τ γ).2 ∘ fwd τ) = id := by
  constructor
  · intro h
    refine ⟨fun γ => ?_, fun γ => ?_⟩
    · have hc := h (γ, id)
      exact congrArg Prod.fst hc
    · have hc := congrArg Prod.snd (h (γ, id))
      exact hc
  · intro ⟨w, hg⟩ ec
    show (track ((τ ec.1).2, fwd τ) ((τ ec.1).1, ec.2 ∘ (τ ec.1).2)) = _
    have hst : (τ ec.1).2 ((τ ec.1).1) = ec.1 := w ec.1
    refine Prod.ext hst ?_
    show (ec.2 ∘ (τ ec.1).2) ∘ fwd τ = ec.2
    funext x
    show ec.2 ((τ ec.1).2 (fwd τ x)) = ec.2 x
    rw [show (τ ec.1).2 (fwd τ x) = x from congrFun (hg ec.1) x]

/-! ## Theorem 16: LIFO reversion along a sequence -/

/-- Apply one effect function to an effect-context state (one step of a
component loading: the yielded inverse is composed onto the accumulator). -/
def applyStep (τ : Eff Γ) (ec : EffectCtx Γ) : EffectCtx Γ :=
  ((τ ec.1).1, ec.2 ∘ (τ ec.1).2)

/-- Apply a sequence of effect functions in order, recording the inverse each
application yielded, in application order. -/
def applyAll : List (Eff Γ) → EffectCtx Γ → EffectCtx Γ × List (Γ → Γ)
  | [], ec => (ec, [])
  | τ :: ts, ec =>
      ((applyAll ts (applyStep τ ec)).1, (τ ec.1).2 :: (applyAll ts (applyStep τ ec)).2)

/-- Revert one recorded inverse of `τ`: the state moves by `g`, and the way to
undo that is the forward map of `τ` again (Definition 12's lifted inverse). -/
def revertStep (τ : Eff Γ) (g : Γ → Γ) (ec : EffectCtx Γ) : EffectCtx Γ :=
  track (g, fwd τ) ec

/-- Revert a whole episode in reverse (LIFO) order, given the effects and the
inverses they yielded, both lists in application order. -/
def revertAll : List (Eff Γ) → List (Γ → Γ) → EffectCtx Γ → EffectCtx Γ
  | [], _, ec => ec
  | τ :: ts, g :: gs, ec => revertStep τ g (revertAll ts gs ec)
  | _ :: _, [], ec => ec

/-- **Theorem 16.** Let witnessed effect functions be applied in order from an
effect context and reverted in the reverse order.  Then each revert recovers
the context state its own application ran against, and every intermediate
state satisfies the soundness invariant: the reversion ends at the state the
applications began from, with the invariant unchanged. -/
theorem revertAll_applyAll (ts : List (Eff Γ)) (hT : ∀ τ ∈ ts, Witnessed τ)
    (ec : EffectCtx Γ) :
    (revertAll ts (applyAll ts ec).2 (applyAll ts ec).1).cur = ec.cur
      ∧ soundness (revertAll ts (applyAll ts ec).2 (applyAll ts ec).1) = soundness ec := by
  induction ts generalizing ec with
  | nil => simp [applyAll, revertAll]
  | cons τ ts ih =>
    have w : Witnessed τ := hT τ (List.mem_cons_self ..)
    have hT' : ∀ σ ∈ ts, Witnessed σ := fun σ hs => hT σ (List.mem_cons_of_mem _ hs)
    have key := ih hT' (applyStep τ ec)
    have hunf : revertAll (τ :: ts) (applyAll (τ :: ts) ec).2 (applyAll (τ :: ts) ec).1
        = track ((τ ec.1).2, fwd τ)
            (revertAll ts (applyAll ts (applyStep τ ec)).2
              (applyAll ts (applyStep τ ec)).1) := rfl
    rw [hunf]
    -- the inner reversion of the tail: by the induction hypothesis it is
    -- back at the state `τ`'s application produced, with its soundness
    -- invariant
    have hcur : (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1).cur = (τ ec.1).1 := key.1
    have hinv : soundness (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1) = soundness (applyStep τ ec) := key.2
    have hg : (τ ec.1).2 ((τ ec.1).1) = ec.1 := w ec.1
    have e1 : (τ ec.1).2 (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1).cur = ec.1 := by rw [hcur]; exact hg
    have e2 : fwd τ ((τ ec.1).2 (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1).cur)
        = (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1).cur := by rw [e1, hcur]; rfl
    constructor
    · -- state component: `g (f γ) = γ` by the witness
      show (track ((τ ec.1).2, fwd τ) (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1)).cur = ec.1
      exact e1
    · -- soundness: `f (g (f γ)) = f γ`, since `g (f γ) = γ` by the witness
      show soundness (track ((τ ec.1).2, fwd τ) (revertAll ts (applyAll ts (applyStep τ ec)).2
          (applyAll ts (applyStep τ ec)).1)) = soundness ec
      calc soundness (track ((τ ec.1).2, fwd τ) (revertAll ts (applyAll ts (applyStep τ ec)).2
            (applyAll ts (applyStep τ ec)).1))
          = (revertAll ts (applyAll ts (applyStep τ ec)).2 (applyAll ts (applyStep τ ec)).1).2
              (fwd τ ((τ ec.1).2 (revertAll ts (applyAll ts (applyStep τ ec)).2
                (applyAll ts (applyStep τ ec)).1).cur)) := rfl
        _ = (revertAll ts (applyAll ts (applyStep τ ec)).2 (applyAll ts (applyStep τ ec)).1).2
              (revertAll ts (applyAll ts (applyStep τ ec)).2
                (applyAll ts (applyStep τ ec)).1).cur := by rw [e2]
        _ = soundness (applyStep τ ec) := hinv
        _ = soundness ec := by
            show ec.2 ((τ ec.1).2 ((τ ec.1).1)) = ec.2 ec.1
            rw [hg]

/-! ## Definitions 17–19: transformation monoids and independence -/

/-- **Definition 17.** The transformation monoid `M(τ)` of an effect function:
the submonoid of `Γ → Γ` generated by the forward map of `τ` and the inverses
`τ` yields at each state. -/
inductive InMonoid (τ : Eff Γ) : (Γ → Γ) → Prop
  | id : InMonoid τ id
  | fwd : InMonoid τ (fwd τ)
  | inv (γ : Γ) : InMonoid τ ((τ γ).2)
  | comp {f g : Γ → Γ} : InMonoid τ f → InMonoid τ g → InMonoid τ (f ∘ g)

/-- Membership in the submonoid generated by the union of two transformation
monoids (the right-hand side of Lemma 18 (2)). -/
inductive InMonoid2 (τ₁ τ₂ : Eff Γ) : (Γ → Γ) → Prop
  | of₁ {f} : InMonoid τ₁ f → InMonoid2 τ₁ τ₂ f
  | of₂ {f} : InMonoid τ₂ f → InMonoid2 τ₁ τ₂ f
  | id : InMonoid2 τ₁ τ₂ id
  | comp {f g} : InMonoid2 τ₁ τ₂ f → InMonoid2 τ₁ τ₂ g → InMonoid2 τ₁ τ₂ (f ∘ g)

/-- Generator-level commutation of two effect functions' transformations:
every generator of `M(τ₁)` commutes with every generator of `M(τ₂)`. -/
def GenComm (τ₁ τ₂ : Eff Γ) : Prop :=
  fwd τ₁ ∘ fwd τ₂ = fwd τ₂ ∘ fwd τ₁
    ∧ (∀ γ, fwd τ₁ ∘ (τ₂ γ).2 = (τ₂ γ).2 ∘ fwd τ₁)
    ∧ (∀ γ, (τ₁ γ).2 ∘ fwd τ₂ = fwd τ₂ ∘ (τ₁ γ).2)
    ∧ (∀ γ γ', (τ₁ γ).2 ∘ (τ₂ γ').2 = (τ₂ γ').2 ∘ (τ₁ γ).2)

/-- **Lemma 18 (1).** If every generator of `M(τ₁)` commutes with every
generator of `M(τ₂)`, then every element of `M(τ₁)` commutes with every
element of `M(τ₂)`. -/
theorem inMonoid_comm {τ₁ τ₂ : Eff Γ} (hc : GenComm τ₁ τ₂) {m₁ : Γ → Γ}
    (h₁ : InMonoid τ₁ m₁) : ∀ {m₂ : Γ → Γ}, InMonoid τ₂ m₂ →
      m₁ ∘ m₂ = m₂ ∘ m₁ := by
  induction h₁ with
  | id => intro _ _; rfl
  | fwd =>
    intro _ h₂
    induction h₂ with
    | id => rfl
    | fwd => exact hc.1
    | inv γ => exact hc.2.1 γ
    | @comp f g _ _ ihf ihg =>
      calc fwd τ₁ ∘ (f ∘ g) = (fwd τ₁ ∘ f) ∘ g := rfl
        _ = (f ∘ fwd τ₁) ∘ g := by rw [ihf]
        _ = f ∘ (fwd τ₁ ∘ g) := rfl
        _ = f ∘ (g ∘ fwd τ₁) := by rw [ihg]
        _ = (f ∘ g) ∘ fwd τ₁ := rfl
  | inv γ =>
    intro _ h₂
    induction h₂ with
    | id => rfl
    | fwd => exact (hc.2.2.1 γ)
    | inv γ' => exact hc.2.2.2 γ γ'
    | @comp f g _ _ ihf ihg =>
      calc (τ₁ γ).2 ∘ (f ∘ g) = ((τ₁ γ).2 ∘ f) ∘ g := rfl
        _ = (f ∘ (τ₁ γ).2) ∘ g := by rw [ihf]
        _ = f ∘ ((τ₁ γ).2 ∘ g) := rfl
        _ = f ∘ (g ∘ (τ₁ γ).2) := by rw [ihg]
        _ = (f ∘ g) ∘ (τ₁ γ).2 := rfl
  | @comp a b _ _ iha ihb =>
    intro m₂ h₂
    calc (a ∘ b) ∘ m₂ = a ∘ (b ∘ m₂) := rfl
      _ = a ∘ (m₂ ∘ b) := by rw [ihb h₂]
      _ = (a ∘ m₂) ∘ b := rfl
      _ = (m₂ ∘ a) ∘ b := by rw [iha h₂]
      _ = m₂ ∘ (a ∘ b) := rfl

/-- **Lemma 18 (2).** The transformation monoid of a composite is contained
in the monoid generated by the union: `M(τ₁ ⋄ τ₂) ⊆ ⟨M(τ₁) ∪ M(τ₂)⟩`. -/
theorem inMonoid_comp_sub (τ₁ τ₂ : Eff Γ) {m : Γ → Γ} (h : InMonoid (τ₁ ⋄ τ₂) m) :
    InMonoid2 τ₁ τ₂ m := by
  have hfwd : InMonoid2 τ₁ τ₂ (fwd τ₁ ∘ fwd τ₂) :=
    .comp (f := fwd τ₁) (g := fwd τ₂) (.of₁ InMonoid.fwd) (.of₂ InMonoid.fwd)
  induction h with
  | id => exact InMonoid2.id
  | fwd => exact (fwd_comp τ₁ τ₂) ▸ hfwd
  | inv γ =>
    -- `(τ₁ ⋄ τ₂) γ = (fwd τ₁ (fwd τ₂ γ), (τ₂ γ).2 ∘ (τ₁ (fwd τ₂ γ)).2)`
    exact InMonoid2.comp (f := (τ₂ γ).2) (g := (τ₁ ((τ₂ γ).1)).2)
      (InMonoid2.of₂ (InMonoid.inv γ)) (InMonoid2.of₁ (InMonoid.inv ((τ₂ γ).1)))
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂

/-- **Definition 19.** Two effect functions are *independent* when
1. every transformation of one commutes with every transformation of the
   other, and
2. neither one's transformations disturb the inverse the other yields. -/
def Independent (τ₁ τ₂ : Eff Γ) : Prop :=
  (∀ {m₁}, InMonoid τ₁ m₁ → ∀ {m₂}, InMonoid τ₂ m₂ → m₁ ∘ m₂ = m₂ ∘ m₁)
    ∧ (∀ {m₁}, InMonoid τ₁ m₁ → ∀ γ : Γ, (τ₂ (m₁ γ)).2 = (τ₂ γ).2)
    ∧ (∀ {m₂}, InMonoid τ₂ m₂ → ∀ γ : Γ, (τ₁ (m₂ γ)).2 = (τ₁ γ).2)

/-- A family of effect functions is *pairwise independent* when any two
distinct members are independent. -/
def PairwiseIndependent {ι : Type} (ts : ι → Eff Γ) : Prop :=
  ∀ i j, i ≠ j → Independent (ts i) (ts j)

end Cordix
