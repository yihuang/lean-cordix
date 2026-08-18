import LeanCordix.Step
import LeanCordix.Iterator

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Cordix

universe u

variable {N K E : Type} [DecidableEq N] [DecidableEq K] {V : K → Type u}

/-! ## Faithful `≈` and local recovery -/

namespace State

/-- The raw table read from a state at a name; an absent name reads as the
empty table. -/
def tableAt (s : State N K E V) (n : N) : CoefCtx K V :=
  match lookup s.reg n with
  | some f => f.table
  | none => fun _ => none

/-- `tableAt` is unchanged by deleting a different name. -/
theorem tableAt_del_ne {r : Registry N K V E} {n m : N} {a : CoefCtx K V}
    (hne : m ≠ n) :
    State.tableAt ⟨del r n, a⟩ m = State.tableAt ⟨r, a⟩ m := by
  simp [State.tableAt, lookup_del_ne hne]

/-- `rawSigma` of a cons is the head table union the tail. -/
theorem rawSigma_cons {N : Type} {K : Type} {V : K → Type u} {E : Type}
    (p : N × Fiber N K V E) (rest : Registry N K V E) (k : K) :
    rawSigma (p :: rest) k = (p.2.table k <|> rawSigma rest k) := by
  rfl

/-- Under pairwise disjoint tables, the head table and the table at another
name cannot both be present. -/
theorem tableAt_disjoint_head {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} {p : N × Fiber N K V E} {rest : Registry N K V E}
    (hdisj : PairwiseDisjointTables (p :: rest)) {n : N} (hpn : p.1 ≠ n) (k : K) :
    p.2.table k = none ∨ State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n k = none := by
  by_cases hlook : (lookup rest n).isSome
  · rcases Option.isSome_iff_exists.mp hlook with ⟨f, hf⟩
    have hmem : (n, f) ∈ rest := lookup_some_mem hf
    have hdisj' := hdisj p (by simp) (n, f) (by simp [hmem]) (by
      intro hEq
      apply hpn
      exact hEq)
    rcases hdisj' k with hnone | hnone'
    · exact Or.inl hnone
    · right
      simp [State.tableAt, hf]
      exact hnone'
  · have hn : lookup rest n = none := Option.not_isSome_iff_eq_none.mp hlook
    right
    simp [State.tableAt, hn]

/-- Deleting a name splits `rawSigma` into that name's table and the rest,
provided distinct fibers have disjoint tables. -/
theorem rawSigma_del_eq_of_disjoint {N : Type} [DecidableEq N] {K : Type}
    {V : K → Type u} {E : Type} (r : Registry N K V E) (hn : NodupKeys r)
    (hdisj : PairwiseDisjointTables r) (n : N) (k : K) :
    rawSigma r k = (State.tableAt ⟨r, (fun _ => none : CoefCtx K V)⟩ n k <|> rawSigma (del r n) k) := by
  induction r with
  | nil => simp [rawSigma, del, State.tableAt, lookup]
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').2
      have hdisjrest : PairwiseDisjointTables rest := by
        intro a ha b hb hab k
        exact hdisj a (by simp [ha]) b (by simp [hb]) hab k
      by_cases h : p.1 = n
      · have hnot : p.1 ∉ rest.map (fun x => x.1) := by
          have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
            simpa [NodupKeys] using hn
          exact (List.nodup_cons.mp hn').1
        have hdel_rest : del rest n = rest := by
          apply del_eq_self_of_not_mem
          simpa [h] using hnot
        rw [rawSigma_cons p rest k]
        rw [show del (p :: rest) n = rest by simp [del, h, hdel_rest]]
        rw [show State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n =
            p.2.table by simp [State.tableAt, lookup, h]]
      · have ih' := ih hnrest hdisjrest
        rw [rawSigma_cons p rest k]
        rw [show del (p :: rest) n = p :: del rest n by simp [del, h]]
        rw [show State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n =
            State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n by
              simp [State.tableAt, lookup, h]]
        rw [rawSigma_cons p (del rest n) k]
        rw [ih']
        have hdisjhead := tableAt_disjoint_head hdisj h k
        rcases hdisjhead with ha | hb
        · simp [ha]
        · simp [hb]

/-- If two duplicate-free, pairwise-disjoint registries have the same
`tableAt` at every name, then their raw sigmas agree. -/
theorem rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint {N : Type} [DecidableEq N]
    {K : Type} [DecidableEq K] {V : K → Type u} {E : Type}
    {r r' : Registry N K V E}
    (hn : NodupKeys r) (hn' : NodupKeys r')
    (hdisj : PairwiseDisjointTables r) (hdisj' : PairwiseDisjointTables r')
    (h : ∀ n, State.tableAt ⟨r, (fun _ => none : CoefCtx K V)⟩ n =
              State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ n) :
    rawSigma r = rawSigma r' := by
  funext k
  induction r generalizing r' with
  | nil =>
      have hnone : rawSigma r' k = none := rawSigma_eq_none_of_all_none (fun p hp => by
        have hk := congrFun (h p.1) k
        have hlook := lookup_self_of_mem_of_nodup hn' hp
        simp [State.tableAt, hlook] at hk
        exact hk.symm)
      simpa [rawSigma] using hnone.symm
  | cons p rest ih =>
      have hnrest : NodupKeys rest := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').2
      have hdisjrest : PairwiseDisjointTables rest := by
        intro a ha b hb hab k
        exact hdisj a (by simp [ha]) b (by simp [hb]) hab k
      have hnot : p.1 ∉ rest.map (fun x => x.1) := by
        have hn' : List.Nodup (p.1 :: rest.map (fun x => x.1)) := by
          simpa [NodupKeys] using hn
        exact (List.nodup_cons.mp hn').1
      have hp_lookup : lookup (p :: rest) p.1 = some p.2 := lookup_self_of_mem_of_nodup hn (by simp)
      have htable_r : State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ p.1 = p.2.table := by
        simp [State.tableAt, hp_lookup]
      have htable_eq : State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ p.1 k = p.2.table k := by
        have heq := congrFun (h p.1) k
        rw [htable_r] at heq
        exact heq.symm
      have hrest_table : ∀ n, State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n =
          State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ n := by
        intro n
        funext k
        by_cases hpn : n = p.1
        · subst n
          have hrest_none : State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ p.1 = fun _ => none := by
            simp [State.tableAt, lookup_none_of_not_mem hnot]
          have hdel_none : State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ p.1 = fun _ => none := by
            simp [State.tableAt, lookup_del_self]
          simp [hrest_none, hdel_none]
        · have hrest_eq : State.tableAt ⟨rest, (fun _ => none : CoefCtx K V)⟩ n =
            State.tableAt ⟨p :: rest, (fun _ => none : CoefCtx K V)⟩ n := by
              simp [State.tableAt, lookup, hpn, Ne.symm hpn]
          have hdel_eq : State.tableAt ⟨del r' p.1, (fun _ => none : CoefCtx K V)⟩ n =
              State.tableAt ⟨r', (fun _ => none : CoefCtx K V)⟩ n := by
                exact State.tableAt_del_ne (n := p.1) (m := n) hpn
          rw [hrest_eq, hdel_eq, h n]
      have ih' := ih (r' := del r' p.1) hnrest (nodupKeys_del hn' p.1)
        hdisjrest (pairwiseDisjointTables_del hdisj' p.1) hrest_table
      rw [rawSigma_cons p rest k]
      rw [rawSigma_del_eq_of_disjoint r' hn' hdisj' p.1 k]
      rw [htable_eq]
      rw [ih']

/-- **Faithful `≈`.** Two states agree on the ambient context and on every
name's raw table, while control fields may differ. -/
structure Approx (s s' : State N K E V) : Prop where
  ambient : s.ambient = s'.ambient
  tables : ∀ n, State.tableAt s n = State.tableAt s' n

namespace Approx

theorem refl (s : State N K E V) : State.Approx s s :=
  ⟨rfl, fun _ => rfl⟩

theorem symm {s s' : State N K E V} (h : State.Approx s s') : State.Approx s' s :=
  ⟨h.ambient.symm, fun n => (h.tables n).symm⟩

theorem trans {s s' s'' : State N K E V} (h : State.Approx s s')
    (h' : State.Approx s' s'') : State.Approx s s'' :=
  ⟨h.ambient.trans h'.ambient, fun n => (h.tables n).trans (h'.tables n)⟩

end Approx

/-- Under duplicate-freeness and pairwise disjoint tables, `≈` implies
`fullCtx` equality. -/
theorem fullCtx_of_nodup_of_disjoint {s t : State N K E V}
    (hs : NodupKeys s.reg) (ht : NodupKeys t.reg)
    (hdisjs : PairwiseDisjointTables s.reg) (hdisjt : PairwiseDisjointTables t.reg)
    (h : State.Approx s t) : State.fullCtx s = State.fullCtx t := by
  apply Prod.ext
  · exact h.ambient
  · exact rawSigma_eq_of_tableAt_eq_of_nodup_of_disjoint hs ht hdisjs hdisjt h.tables

/-- `ConfinedEffect` transfers from `y` to an `≈`-equivalent state `z`
with the same fiber at the acting name. -/
theorem confinedEffect_transfer_of_approx {y z : State N K E V} {m : N}
    {δ : Ctx K V}
    (hyz : State.Approx y z)
    (hfull : State.fullCtx y = State.fullCtx z)
    (hdom : (lookup y.reg m).isSome ↔ (lookup z.reg m).isSome)
    (hprov : ∀ gy gz, lookup y.reg m = some gy → lookup z.reg m = some gz →
      gy.comp.prov = gz.comp.prov)
    (hnody : NodupKeys y.reg) (hnodz : NodupKeys z.reg)
    (hconf : ConfinedEffect y m δ) :
    ConfinedEffect z m δ := by
  rcases hconf with ⟨fy, hfy, hout, hsupport, hdisj⟩
  have hz_some : (lookup z.reg m).isSome := by
    rw [← hdom]
    exact Option.isSome_iff_exists.mpr ⟨fy, hfy⟩
  rcases Option.isSome_iff_exists.mp hz_some with ⟨fz, hfz⟩
  have hprov_eq : fz.comp.prov = fy.comp.prov := (hprov fy fz hfy hfz).symm
  refine ⟨fz, hfz, ?_, ?_, ?_⟩
  · intro k hk
    have hk_y : k ∉ fy.comp.prov := by simpa [hprov_eq] using hk
    have hraw : rawSigma y.reg k = rawSigma z.reg k := by
      have hsnd := congrArg Prod.snd hfull
      exact congrFun hsnd k
    exact (hraw.symm.trans (hout k hk_y))
  · intro k hk
    have hk_y : k ∉ fy.comp.prov := by simpa [hprov_eq] using hk
    have htable_z_symm : fy.table = fz.table := by
      simpa [State.tableAt, hfy, hfz] using hyz.tables m
    have htable_z : fz.table = fy.table := htable_z_symm.symm
    rw [htable_z]
    exact hsupport k hk_y
  · intro p hp hpm k hk
    have hk_y : k ∈ fy.comp.prov := by simpa [hprov_eq] using hk
    have hlook_z : lookup z.reg p.1 = some p.2 := lookup_self_of_mem_of_nodup hnodz hp
    have htable_yz : State.tableAt y p.1 k = State.tableAt z p.1 k := congrFun (hyz.tables p.1) k
    have hz_table : State.tableAt z p.1 k = p.2.table k := by
      simp [State.tableAt, hlook_z]
    have htable_eq : State.tableAt y p.1 k = p.2.table k := htable_yz.trans hz_table
    by_cases hy : (lookup y.reg p.1).isSome
    · rcases Option.isSome_iff_exists.mp hy with ⟨gy, hgy⟩
      have htable_y : State.tableAt y p.1 k = gy.table k := by
        simp [State.tableAt, hgy]
      have hp_eq : p.2.table k = gy.table k := (htable_y.symm.trans htable_eq).symm
      have hp_y : (p.1, gy) ∈ y.reg := lookup_some_mem hgy
      have hnone : gy.table k = none := hdisj (p.1, gy) hp_y (by intro heq; exact hpm heq) k hk_y
      rw [hp_eq, hnone]
    · have hyn : lookup y.reg p.1 = none := Option.not_isSome_iff_eq_none.mp hy
      have htable_y : State.tableAt y p.1 k = none := by
        simp [State.tableAt, hyn]
      exact (htable_y.symm.trans htable_eq).symm

/-- A write-confined iterator still produces a confined effect after
recovering another fiber `n`. -/
theorem confinedEffect_of_confinedIterator_of_recover {s : State N K E V}
    {m n : N} {ι : Iterator (Ctx K V) E} {δ δ₀ : Ctx K V}
    (hmn : m ≠ n) (hnodup : NodupKeys s.reg)
    (hconf : ConfinedEffect s m δ₀)
    (hι : ∀ f, lookup s.reg m = some f → ConfinedIterator ι f.comp.prov)
    (hstep : ∃ h c, Iterator.step ι (State.fullCtx (State.recover s n)) = .ok (δ, h, c)) :
    ConfinedEffect (State.recover s n) m δ := by
  rcases hconf with ⟨f, hf, hout₀, hsupport, hdisj⟩
  have hfrec : lookup (State.recover s n).reg m = some f := by
    rw [State.lookup_recover_ne (n := n) (m := m) (Ne.symm hmn), hf]
  have hdisjrec := recover_preserves_confined_disjoint (m := m) (n := n) (f := f) hmn hnodup hf hdisj
  exact confinedEffect_of_confinedIterator hfrec (hι f hf) hstep hsupport hdisjrec

/-- A write-confined accumulator still produces a confined effect after
recovering another fiber `n`. -/
theorem confinedEffect_of_confinedAcc_of_recover {s : State N K E V}
    {m n : N} {κ : Ctx K V → Ctx K V} {δ₀ : Ctx K V}
    (hmn : m ≠ n) (hnodup : NodupKeys s.reg)
    (hconf : ConfinedEffect s m δ₀)
    (hκ : ∀ f, lookup s.reg m = some f → ConfinedAcc κ f.comp.prov) :
    ConfinedEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
  rcases hconf with ⟨f, hf, hout₀, hsupport, hdisj⟩
  have hfrec : lookup (State.recover s n).reg m = some f := by
    rw [State.lookup_recover_ne (n := n) (m := m) (Ne.symm hmn), hf]
  have hdisjrec := recover_preserves_confined_disjoint (m := m) (n := n) (f := f) hmn hnodup hf hdisj
  exact confinedEffect_of_confinedAcc hfrec (hκ f hf) hsupport hdisjrec

/-- `tableAt` after a pointwise `set` at the updated name. -/
theorem tableAt_set_eq (r : Registry N K V E) (n : N) (g : Fiber N K V E)
    (a : CoefCtx K V) :
    State.tableAt ⟨set r n g, a⟩ n = g.table := by
  simp [State.tableAt, lookup_set_eq]

/-- `tableAt` after a pointwise `set` away from the updated name. -/
theorem tableAt_set_ne (r : Registry N K V E) (n m : N) (g : Fiber N K V E)
    (a : CoefCtx K V) (hmn : m ≠ n) :
    State.tableAt ⟨set r n g, a⟩ m = State.tableAt ⟨r, a⟩ m := by
  simp [State.tableAt, lookup_set_ne r n m g hmn]

/-- `writeEffect` at the same name preserves `≈`, provided the acting name
has the same presence and the same provision in both input states. -/
theorem writeEffect_preserves_approx {x y : State N K E V} {n : N}
    (h : State.Approx x y) (δ : Ctx K V)
    (hdom : (lookup x.reg n).isSome ↔ (lookup y.reg n).isSome)
    (hprov : ∀ gx gy, lookup x.reg n = some gx → lookup y.reg n = some gy →
      gx.comp.prov = gy.comp.prov) :
    State.Approx (State.writeEffect x n δ) (State.writeEffect y n δ) := by
  constructor
  · unfold State.writeEffect
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      simp [hfx, hfy]
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [hxn, hyn, h.ambient]
  · intro m
    unfold State.writeEffect
    by_cases hx : (lookup x.reg n).isSome
    · have hy : (lookup y.reg n).isSome := hdom.mp hx
      rcases Option.isSome_iff_exists.mp hx with ⟨fx, hfx⟩
      rcases Option.isSome_iff_exists.mp hy with ⟨fy, hfy⟩
      by_cases hmn : m = n
      · subst m
        simp [State.tableAt, hfx, hfy, lookup_set_eq, hprov fx fy hfx hfy]
      · rw [hfx, hfy]
        rw [State.tableAt_set_ne x.reg n m
          (Fiber.mk fx.comp fx.parent (splitTable fx.comp.prov δ.2) fx.retired fx.lc) δ.1 hmn]
        rw [State.tableAt_set_ne y.reg n m
          (Fiber.mk fy.comp fy.parent (splitTable fy.comp.prov δ.2) fy.retired fy.lc) δ.1 hmn]
        exact h.tables m
    · have hy : ¬ (lookup y.reg n).isSome := by intro hy; exact hx (hdom.mpr hy)
      have hxn : lookup x.reg n = none := Option.not_isSome_iff_eq_none.mp hx
      have hyn : lookup y.reg n = none := Option.not_isSome_iff_eq_none.mp hy
      simp [State.tableAt, hxn, hyn]
      exact h.tables m

/-- `recover` at `n` does not change the raw table at a different name. -/
theorem tableAt_recover_ne {s : State N K E V} {n m : N}
    (hmn : n ≠ m) :
    State.tableAt (State.recover s n) m = State.tableAt s m := by
  unfold State.tableAt
  rw [State.lookup_recover_ne hmn]

/-- `recover` at an installed (non-inactive) fiber empties that fiber's
table. -/
theorem tableAt_recover_eq_of_not_inactive {s : State N K E V} {n : N}
    {f : Fiber N K V E} (hf : lookup s.reg n = some f)
    (hni : ∀ o, f.lc ≠ .inactive o) :
    State.tableAt (State.recover s n) n = fun _ => none := by
  unfold State.recover
  rw [hf]
  cases hlc : f.lc with
  | inactive o => exact False.elim (hni o hlc)
  | loading i κ v => simp [State.tableAt, lookup_set_eq, hlc]
  | active κ v => simp [State.tableAt, lookup_set_eq, hlc]
  | unloading κ v o => simp [State.tableAt, lookup_set_eq, hlc]

/-- `writeEffect` at a present fiber writes the split table at that fiber. -/
theorem tableAt_writeEffect_eq {s : State N K E V} {m : N} {g : Fiber N K V E}
    (hg : lookup s.reg m = some g) (δ : Ctx K V) :
    State.tableAt (State.writeEffect s m δ) m = splitTable g.comp.prov δ.2 := by
  unfold State.writeEffect
  rw [hg]
  exact State.tableAt_set_eq s.reg m { g with table := splitTable g.comp.prov δ.2 } δ.1

/-- `writeEffect` at `m` does not change the raw table at another name. -/
theorem tableAt_writeEffect_ne {s : State N K E V} {m x : N} {g : Fiber N K V E}
    (hg : lookup s.reg m = some g) (hmx : x ≠ m) (δ : Ctx K V) :
    State.tableAt (State.writeEffect s m δ) x = State.tableAt s x := by
  unfold State.writeEffect
  rw [hg]
  exact State.tableAt_set_ne s.reg m x { g with table := splitTable g.comp.prov δ.2 } δ.1 hmx

/-- If the ambient of `κ_n δ` is `δ'.1` and the table split at `m` is
unchanged, then `recover n` commutes with `writeEffect m` for distinct
`n` and `m`, up to `≈`. -/
theorem recover_writeEffect_approx {s : State N K E V} {n m : N}
    (hmn : n ≠ m) (δ δ' : Ctx K V)
    (hnodup : NodupKeys s.reg)
    (hconfm : ConfinedEffect s m δ)
    (hamb : (State.accAt s n δ).1 = δ'.1)
    (htable : ∀ g, lookup s.reg m = some g →
      splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ'.2)
    {f : Fiber N K V E} (hf : lookup s.reg n = some f)
    (hni : ∀ o, f.lc ≠ .inactive o) :
    State.Approx (State.recover (State.writeEffect s m δ) n)
      (State.writeEffect (State.recover s n) m δ') := by
  have hlook : lookup (State.writeEffect s m δ).reg n = some f :=
    State.lookup_writeEffect_ne hmn hf δ
  constructor
  · -- ambient
    have hfull : State.fullCtx (State.writeEffect s m δ) = δ :=
      State.fullCtx_writeEffect_of_confined hnodup hconfm
    rcases hconfm with ⟨g, hg, _⟩
    cases hlc : f.lc with
    | inactive o => exact False.elim (hni o hlc)
    | loading i κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_loading_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_loading_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
    | active κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_active_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_active_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
    | unloading κ v o =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_unloading_eq hlook (by simpa using hlc)
        rw [hrec']
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_unloading_eq hf hlc
        rw [hrec]
        simp [State.writeEffect,
          lookup_set_ne s.reg n m ({ f with table := fun _ => none } : Fiber N K V E) (Ne.symm hmn),
          hg]
        rw [← State.writeEffect_eq_of_lookup hg δ]
        rw [hfull]
        have hκ : κ = State.accAt s n := by
          rw [State.accAt_eq hf]
          simp [Lifecycle.acc, hlc]
        rw [hκ, hamb]
  · -- tables
    cases hlc : f.lc with
    | inactive o => exact False.elim (hni o hlc)
    | loading i κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_loading_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_loading_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']
    | active κ v =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_active_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_active_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']
    | unloading κ v o =>
        have hrec' : State.recover (State.writeEffect s m δ) n =
            ⟨set (State.writeEffect s m δ).reg n { f with table := fun _ => none },
              (κ (State.fullCtx (State.writeEffect s m δ))).1⟩ :=
          State.recover_unloading_eq hlook (by simpa using hlc)
        have hrec : State.recover s n =
            ⟨set s.reg n { f with table := fun _ => none }, (κ (State.fullCtx s)).1⟩ :=
          State.recover_unloading_eq hf hlc
        intro x
        by_cases hxn : x = n
        · subst x
          rw [hrec', hrec]
          by_cases hm : (lookup s.reg m).isSome
          · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
            simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
              hg, hmn, Ne.symm hmn]
          · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
            simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
        · by_cases hxm : x = m
          · subst x
            rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_eq, lookup_set_ne,
                hg, htable g hg, hmn, Ne.symm hmn]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hm']
          · rw [hrec', hrec]
            by_cases hm : (lookup s.reg m).isSome
            · rcases Option.isSome_iff_exists.mp hm with ⟨g, hg⟩
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hg, hmn, Ne.symm hmn,
                hxn, hxm]
            · have hm' : lookup s.reg m = none := Option.not_isSome_iff_eq_none.mp hm
              simp [State.writeEffect, State.tableAt, lookup_set_ne, hmn, Ne.symm hmn, hxn, hxm, hm']

/-- **Theorem 61, faithful step commutation.**  If the component iterators of
`n` and of the step's acting fiber are independent, the accumulated maps lie
in the corresponding transformation monoids, and the tracked fiber `n` is
open with the withdrawal invariants, then full recovery at `n` commutes with
the step's `Ψ` up to `≈`. -/
theorem recover_psi_commute_approx_of_indep {s : State N K E V} (st : Step s)
    {n : N} (hne : n ≠ st.name)
    (iterOf : N → Iterator (Ctx K V) E)
    (hind : Iterator.Independent (iterOf n) (iterOf st.name))
    (hiter : ∀ f, lookup s.reg st.name = some f → iterOf st.name = f.comp.iter)
    (hn_mem : Iterator.InTransformMonoid (iterOf n) (State.accAt s n))
    (hm_mem : ∀ f, lookup s.reg st.name = some f →
        Iterator.InTransformMonoid (iterOf st.name) (Lifecycle.acc f.lc))
    (hnodup : NodupKeys s.reg)
    (hwithdraw : State.Withdraws s n)
    (hwithdraw_on : ∀ f, lookup s.reg st.name = some f →
        State.WithdrawsOn s n f.comp.prov)
    (hopen : ∃ f, lookup s.reg n = some f ∧ ∀ o, f.lc ≠ .inactive o)
    (hconf : Step.Confined st) :
    State.Approx (State.recover (Step.psi st s) n)
      (Step.psi st (State.recover s n)) := by
  cases st with
  | oInsert m c p hn hp hdisj =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | oRetire m f hf =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | oRemove m f o hf hl hchild =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lBegin m f v hf hl ht htable =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lIter m f ι κ v ι' δ h hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, some ι') := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lIter m f ι κ v ι' δ h hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lFinish m f ι κ v δ h hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, none) := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lFinish m f ι κ v δ h hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lRaise m f ι κ v e hreach hf hl hstep =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lDivertAbort m f ι κ v hreach hf hl ht =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lDivertLand m f ι κ v δ h c hreach hf hl ht hstep =>
      have hconfm : ConfinedEffect s m δ := hconf
      have hpsi : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) s = State.writeEffect s m δ := by
        simp [Step.psi, hstep]
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hstep' : Iterator.step ι (State.fullCtx (State.recover s n)) =
          .ok (δ, h, c) := by
        rw [hwithdraw]
        rw [hind'.2.2 hn_mem (by simpa [hiter'] using hreach) (State.fullCtx s)]
        exact hstep
      have hpsi' : Step.psi (Step.lDivertLand m f ι κ v δ h c hreach hf hl ht hstep) (State.recover s n) =
          State.writeEffect (State.recover s n) m δ := by
        simp [Step.psi, hstep']
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hφ : Iterator.stepFwd ι (State.fullCtx s) = δ := by
        simp [Iterator.stepFwd, hstep]
      have hφ' : Iterator.stepFwd ι (State.fullCtx (State.recover s n)) = δ := by
        simp [Iterator.stepFwd, hstep']
      have hfwd_mem : Iterator.InTransformMonoid (iterOf m) (Iterator.stepFwd ι) := by
        exact Iterator.InTransformMonoid.fwd (by simpa [hiter'] using hreach)
      have hcomm := hind'.1 hn_mem hfwd_mem
      have hamb : (State.accAt s n δ).1 = δ.1 := by
        rw [← hφ]
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        rw [hφ'] at h
        rw [← hφ] at h
        exact h
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov δ.2 = splitTable g.comp.prov δ.2 := by
        intro g hg; rfl
      exact State.recover_writeEffect_approx hne δ δ hnodup hconfm hamb htable hfn hni
  | lLeave m f κ v hf hl ht =>
      simpa [Step.psi] using State.Approx.refl (State.recover s n)
  | lUnload m f κ v o hf hl hg =>
      have hne_m : n ≠ m := by simpa [Step.name] using hne
      have hconfm : ConfinedEffect s m (κ (State.fullCtx s)) := hconf
      have hpsi : Step.psi (Step.lUnload m f κ v o hf hl hg) s =
          State.writeEffect s m (κ (State.fullCtx s)) := by
        simp [Step.psi, hf]
      have hpsi' : Step.psi (Step.lUnload m f κ v o hf hl hg) (State.recover s n) =
          State.writeEffect (State.recover s n) m (κ (State.fullCtx (State.recover s n))) := by
        simp [Step.psi, State.lookup_recover_ne hne_m, hf]
      rw [hpsi, hpsi']
      rcases hopen with ⟨fn, hfn, hni⟩
      have hind' : Iterator.Independent (iterOf n) (iterOf m) := by
        simpa [Step.name] using hind
      have hiter' : iterOf m = f.comp.iter := by
        simpa [Step.name] using hiter f hf
      have hκm_mem : Iterator.InTransformMonoid (iterOf m) κ := by
        have h := hm_mem f hf
        simpa [Step.name, Lifecycle.acc, hl, hiter'] using h
      have hcomm := hind'.1 hn_mem hκm_mem
      have hamb : (State.accAt s n (κ (State.fullCtx s))).1 =
          (κ (State.fullCtx (State.recover s n))).1 := by
        have h := congrArg (fun g => (g (State.fullCtx s)).1) hcomm
        simp only [Function.comp_apply] at h
        rw [← hwithdraw] at h
        exact h
      have hw : ∀ γ, splitTable f.comp.prov ((State.accAt s n γ).2) =
          splitTable f.comp.prov γ.2 := by
        have hw0 : ∀ γ, splitTable f.comp.prov ((Lifecycle.acc fn.lc γ).2) =
            splitTable f.comp.prov γ.2 := by
          simpa [State.WithdrawsOn, hfn] using hwithdraw_on f hf
        intro γ
        simpa [State.accAt, hfn] using hw0 γ
      have htable : ∀ g, lookup s.reg m = some g →
          splitTable g.comp.prov (κ (State.fullCtx s)).2 =
            splitTable g.comp.prov (κ (State.fullCtx (State.recover s n))).2 := by
        intro g hg
        have hgf : g = f :=
          (lookup_eq_of_nodup (r := s.reg) (n := m) (f := f) (g := g) hnodup hf hg).symm
        subst g
        rw [hwithdraw]
        have hcomm' := congrArg (fun g => (g (State.fullCtx s)).2) hcomm
        simp only [Function.comp_apply] at hcomm'
        have hsplit : splitTable f.comp.prov ((State.accAt s n (κ (State.fullCtx s))).2) =
            splitTable f.comp.prov ((κ (State.accAt s n (State.fullCtx s))).2) := by
          rw [hcomm']
        have hw' := hw (κ (State.fullCtx s))
        exact (hw'.symm.trans hsplit)
      exact State.recover_writeEffect_approx hne_m (κ (State.fullCtx s))
        (κ (State.fullCtx (State.recover s n))) hnodup hconfm hamb htable hfn hni

end State
end Cordix
