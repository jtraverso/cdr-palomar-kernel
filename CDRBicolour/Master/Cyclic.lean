/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Master.Equitable
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Stage 1 with `B = A + 1`: explicit cyclic colourings

When `B = A + 1` every vertex of `K_A` misses exactly two of the `B` colours, so the ABB rows are
single pairs and the only requirement is that the missing pairs be distinct.  Two explicit
colourings achieve this:

* `A` odd: colour `{u, v}` by `u + v ∈ ℤ/A`, plus an extra colour `∞`; `u` misses `{2u, ∞}`;
* `A` even: the round-robin 1-factorization of `K_{A+2}` on `ℤ/(A+1) ∪ {∞}` (`{i,j} ↦ i + j`,
  `{∞, i} ↦ 2i`) with the two vertices `0, 1` removed; `i` misses `{i, i+1}`, `∞` misses
  `{0, 2}`.

`x1_realises`: with the master criterion's stages 2–4 (`master_of_stage1`), every admissible
profile `(A, A+1, C)` with `C` even, `A + 4 ≤ C`, `6(C-A-1) ≤ C`, `6C ≤ 7A` is realised.
-/

@[expose] public section

namespace CDRBicolour.Master

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix CDRBicolour.L184

/-- A symmetric colouring of `K_X` by `Y` which is proper, and whose missing sets are distinct
pairs `{p u, q u}`. -/
def Stage1Pairs (X Y : Type*) : Prop :=
  ∃ (g : X → X → Y) (p q : X → Y), (∀ u v, g u v = g v u) ∧
    (∀ u v w, v ≠ u → w ≠ u → g u v = g u w → v = w) ∧ (∀ u, p u ≠ q u) ∧
    (∀ u c, (∀ v, v ≠ u → g u v ≠ c) ↔ (c = p u ∨ c = q u)) ∧
    (∀ u w, u ≠ w → s(p u, q u) ≠ s(p w, q w))

theorem Stage1Pairs.transport {X Y X' Y' : Type*} (eA : X' ≃ X) (eB : Y' ≃ Y)
    (h : Stage1Pairs X Y) : Stage1Pairs X' Y' := by
  obtain ⟨g, p, q, hg, hinj, hpq, hmiss, hdist⟩ := h
  refine ⟨fun u v => eB.symm (g (eA u) (eA v)), fun u => eB.symm (p (eA u)),
    fun u => eB.symm (q (eA u)), fun u v => by dsimp only; rw [hg], ?_, ?_, ?_, ?_⟩
  · intro u v w hv hw h
    exact eA.injective (hinj _ _ _ (fun h' => hv (eA.injective h'))
      (fun h' => hw (eA.injective h')) (eB.symm.injective h))
  · intro u h; exact hpq _ (eB.symm.injective h)
  · intro u c
    have := hmiss (eA u) (eB c)
    constructor
    · intro hv
      have h1 : ∀ x, x ≠ eA u → g (eA u) x ≠ eB c := by
        intro x hx hgx
        apply hv (eA.symm x) (fun h' => hx (by rw [← h', Equiv.apply_symm_apply]))
        dsimp only; rw [Equiv.apply_symm_apply, hgx, Equiv.symm_apply_apply]
      rcases this.1 h1 with h2 | h2
      · left; dsimp only; rw [← h2, Equiv.symm_apply_apply]
      · right; dsimp only; rw [← h2, Equiv.symm_apply_apply]
    · intro hc v hv hgv
      have h2 : eB c = p (eA u) ∨ eB c = q (eA u) := by
        rcases hc with rfl | rfl <;> simp
      exact this.2 h2 (eA v) (fun h' => hv (eA.injective h')) (by rw [← hgv]; simp)
  · intro u w huw h
    apply hdist (eA u) (eA w) (fun h' => huw (eA.injective h'))
    have := congrArg (Sym2.map eB) h
    simpa using this

/-- From `Stage1Pairs` to the stage-1 data of the master criterion. -/
theorem stage1_of_pairs {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (h : Stage1Pairs X Y) :
    ∃ (χ : Sym2 X → Y) (M : X → Finset (Sym2 Y)),
      ProperOn (⊤ : SimpleGraph X).edgeFinset χ ∧ (∀ i, IsPerfectPairing (M i) (miss ⊤ χ i)) ∧
        PairDisjoint M := by
  classical
  obtain ⟨g, p, q, hg, hinj, hpq, hmiss, hdist⟩ := h
  let χ : Sym2 X → Y := Sym2.lift ⟨g, hg⟩
  have hχ : ∀ u v, χ s(u, v) = g u v := fun u v => rfl
  have hinc : ∀ u e, e ∈ (⊤ : SimpleGraph X).incidenceFinset u ↔ ∃ v, v ≠ u ∧ e = s(u, v) := by
    intro u e
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨he, hu⟩
      obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.1 hu
      exact ⟨v, fun h => (SimpleGraph.mem_edgeSet _).1 he (h ▸ rfl), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(SimpleGraph.mem_edgeSet _).2 (Ne.symm hv), Sym2.mem_mk_left _ _⟩
  have hmem : ∀ u c, c ∈ miss ⊤ χ u ↔ (c = p u ∨ c = q u) := by
    intro u c
    rw [mem_miss, ← hmiss]
    constructor
    · intro h v hv; exact h s(u, v) ((hinc u _).2 ⟨v, hv, rfl⟩)
    · intro h e he
      obtain ⟨v, hv, rfl⟩ := (hinc u e).1 he
      exact h v hv
  refine ⟨χ, fun u => {s(p u, q u)}, ?_, ?_, ?_⟩
  · intro e he f hf hne hcol
    rw [Finset.disjoint_left]
    intro x hxe hxf
    rw [Sym2.mem_toFinset] at hxe hxf
    obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.1 hxe
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hxf
    have hv : v ≠ x := fun h => SimpleGraph.not_isDiag_of_mem_edgeFinset he (by rw [h]; rfl)
    have hw : w ≠ x := fun h => SimpleGraph.not_isDiag_of_mem_edgeFinset hf (by rw [h]; rfl)
    exact hne (by rw [hinj x v w hv hw hcol])
  · intro u
    refine ⟨?_, ?_, ?_⟩
    · intro e he; rw [mem_singleton] at he; subst he
      rw [Sym2.mk_isDiag_iff]; exact hpq u
    · intro e he c hc; rw [mem_singleton] at he; subst he
      rw [hmem]; rcases Sym2.mem_iff.1 hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro c hc
      refine ⟨s(p u, q u), ⟨mem_singleton_self _, ?_⟩, fun e he => mem_singleton.1 he.1⟩
      rcases (hmem u c).1 hc with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
  · intro u w huw
    exact disjoint_singleton.2 (hdist u w huw)

/-- `2` is cancellable in `ℤ/N`, `N` odd. -/
theorem two_mul_cancel {N : ℕ} (hN : N % 2 = 1) {x y : ZMod N} (h : 2 * x = 2 * y) : x = y := by
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.2 (Nat.odd_iff.2 hN)
  have hu : IsUnit (2 : ZMod N) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  exact hu.mul_left_cancel h

/-- `A` odd: `ℤ/A` with the colours `ℤ/A ∪ {∞}`. -/
theorem stage1Pairs_odd (A : ℕ) [NeZero A] (hA : A % 2 = 1) :
    Stage1Pairs (ZMod A) (Option (ZMod A)) := by
  classical
  refine ⟨fun u v => some (u + v), fun _ => none, fun u => some (u + u), fun u v => by
    dsimp only; rw [add_comm], ?_, fun u => by simp, ?_, ?_⟩
  · intro u v w _ _ h; simpa using h
  · intro u c
    rcases c with _ | z
    · simp
    · simp only [ne_eq, Option.some.injEq, reduceCtorEq, false_or]
      constructor
      · intro h
        by_contra hz
        exact h (z - u) (fun h' => hz (by linear_combination h')) (by ring)
      · rintro rfl v hv h
        exact hv (add_left_cancel h)
  · intro u w huw h
    dsimp only at h
    rw [Sym2.congr_right, Option.some.injEq, ← two_mul, ← two_mul] at h
    exact huw (two_mul_cancel hA h)

/-- The vertex set of the even construction: `ℤ/N ∖ {0, 1}` plus `∞`. -/
abbrev EvenVert (N : ℕ) := Option {z : ZMod N // z ≠ 0 ∧ z ≠ 1}

/-- The round-robin colour of an edge of `K_{N+1}` on `ℤ/N ∪ {∞}`. -/
def rrColour {N : ℕ} : EvenVert N → EvenVert N → ZMod N
  | some i, some j => i.1 + j.1
  | none, some j => 2 * j.1
  | some i, none => 2 * i.1
  | none, none => 0

/-- `N` odd, `N ≥ 5`: the round-robin factorization minus the vertices `0, 1`. -/
theorem stage1Pairs_even (N : ℕ) [NeZero N] (hN : N % 2 = 1) (h5 : 5 ≤ N) :
    Stage1Pairs (EvenVert N) (ZMod N) := by
  classical
  have h2 : (2 : ZMod N) ≠ 0 := by
    intro h; have := (ZMod.natCast_eq_zero_iff 2 N).1 (by exact_mod_cast h)
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  have h3 : (3 : ZMod N) ≠ 0 := by
    intro h; have := (ZMod.natCast_eq_zero_iff 3 N).1 (by exact_mod_cast h)
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  have h1 : (1 : ZMod N) ≠ 0 := by
    intro h; have := (ZMod.natCast_eq_zero_iff 1 N).1 (by exact_mod_cast h)
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.2 (Nat.odd_iff.2 hN)
  have hu : IsUnit (2 : ZMod N) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  let pv : EvenVert N → ZMod N := fun x => match x with | some i => i.1 | none => 0
  let qv : EvenVert N → ZMod N := fun x => match x with | some i => i.1 + 1 | none => 2
  refine ⟨rrColour, pv, qv, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | i) (_ | j) <;> simp [rrColour, add_comm]
  · rintro (_ | i) (_ | v) (_ | w) hv hw h <;> simp only [rrColour] at h
    · exact absurd rfl hv
    · exact absurd rfl hv
    · exact absurd rfl hw
    · exact congrArg some (Subtype.ext (two_mul_cancel hN h))
    · rfl
    · have : (w : ZMod N) = i := by linear_combination -h
      exact absurd (congrArg some (Subtype.ext this)) hw
    · have : (v : ZMod N) = i := by linear_combination h
      exact absurd (congrArg some (Subtype.ext this)) hv
    · exact congrArg some (Subtype.ext (add_left_cancel h))
  · rintro (_ | i)
    · simpa [pv, qv] using h2.symm
    · simp only [pv, qv, ne_eq]
      intro h; exact h1 (by linear_combination -h)
  · rintro (_ | ⟨i, hi0, hi1⟩) c
    · simp only [pv, qv]
      constructor
      · intro h
        by_contra hc; push Not at hc
        refine h (some ⟨t * c, ?_, ?_⟩) (by simp) ?_
        · intro h0; apply hc.1; linear_combination (-c) * ht + 2 * h0
        · intro h0; apply hc.2; linear_combination (-c) * ht + 2 * h0
        · simp only [rrColour]; linear_combination c * ht
      · rintro hc (_ | ⟨j, hj0, hj1⟩) hv h
        · exact hv rfl
        · simp only [rrColour] at h
          rcases hc with rfl | rfl
          · exact hj0 (two_mul_cancel hN (by rw [h, mul_zero]))
          · exact hj1 (two_mul_cancel hN (by rw [h, mul_one]))
    · simp only [pv, qv]
      constructor
      · intro h
        by_contra hc; push Not at hc
        by_cases h2i : c = 2 * i
        · exact h none (by simp) (by simp [rrColour, h2i])
        · refine h (some ⟨c - i, ?_, ?_⟩) ?_ ?_
          · intro h0; apply hc.1; linear_combination h0
          · intro h0; apply hc.2; linear_combination h0
          · intro h0
            apply h2i
            have := congrArg (fun x => Option.map Subtype.val x) h0
            simp only [Option.map_some, Option.some.injEq] at this
            linear_combination this
          · simp only [rrColour]; ring
      · rintro hc (_ | ⟨j, hj0, hj1⟩) hv h
        · simp only [rrColour] at h
          rcases hc with rfl | rfl
          · apply hi0; linear_combination h
          · apply hi1; linear_combination h
        · simp only [rrColour] at h
          rcases hc with rfl | rfl
          · exact hj0 (by linear_combination h)
          · exact hj1 (by linear_combination h)
  · rintro (_ | ⟨i, hi0, hi1⟩) (_ | ⟨j, hj0, hj1⟩) huw h
    · exact huw rfl
    · simp only [pv, qv, Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, h'⟩
      · exact hj0 h.symm
      · exact h3 (by linear_combination h' - h)
    · simp only [pv, qv, Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, h'⟩
      · exact hi0 h
      · exact h3 (by linear_combination h' - h)
    · simp only [pv, qv, Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, h'⟩
      · exact huw (by rw [Option.some.injEq]; exact Subtype.ext h)
      · exact h2 (by linear_combination h' - h)

/-- `|ℤ/N ∖ {0, 1}| = N - 2`. -/
theorem card_evenVert (N : ℕ) [NeZero N] (h5 : 5 ≤ N) : Fintype.card (EvenVert N) = N - 1 := by
  classical
  have h1 : (1 : ZMod N) ≠ 0 := by
    intro h; have := (ZMod.natCast_eq_zero_iff 1 N).1 (by exact_mod_cast h)
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  rw [Fintype.card_option, Fintype.card_subtype]
  have : (univ.filter fun z : ZMod N => z ≠ 0 ∧ z ≠ 1) = (univ.erase 0).erase 1 := by
    ext z; simp [and_comm]
  rw [this, card_erase_of_mem (by simp [h1]), card_erase_of_mem (mem_univ _), card_univ,
    ZMod.card]
  omega

/-- Stage 1 for `B = A + 1` (`A ≥ 4`), on any types of the right sizes. -/
theorem stage1_succ {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {A : ℕ} (hA4 : 4 ≤ A) (hX : Fintype.card X = A) (hY : Fintype.card Y = A + 1) :
    ∃ (χ : Sym2 X → Y) (M : X → Finset (Sym2 Y)),
      ProperOn (⊤ : SimpleGraph X).edgeFinset χ ∧ (∀ i, IsPerfectPairing (M i) (miss ⊤ χ i)) ∧
        PairDisjoint M := by
  classical
  rcases Nat.even_or_odd A with hA | hA
  · haveI : NeZero (A + 1) := ⟨by omega⟩
    have hcard := card_evenVert (A + 1) (by omega)
    have hP := stage1Pairs_even (A + 1) (by rcases hA with ⟨k, hk⟩; omega) (by omega)
    exact stage1_of_pairs (hP.transport (Fintype.equivOfCardEq (by rw [hX, hcard]; omega))
      (Fintype.equivOfCardEq (by rw [hY, ZMod.card])))
  · haveI : NeZero A := ⟨by omega⟩
    have hP := stage1Pairs_odd A (Nat.odd_iff.1 hA)
    exact stage1_of_pairs (hP.transport (Fintype.equivOfCardEq (by rw [hX, ZMod.card]))
      (Fintype.equivOfCardEq (by rw [hY, Fintype.card_option, ZMod.card])))

/-- **The family `B = A + 1`** through the master criterion's stages 2–4. -/
theorem x1_realises {A B C : ℕ}
    (hadm : AdmissibleProfile A B C) (hB : B = A + 1) (hC : C % 2 = 0) (h4 : A + 4 ≤ C)
    (hA4 : 4 ≤ A) (hρ6 : 6 * (C - A - 1) ≤ C) (h76 : 6 * C ≤ 7 * A) : Realises A B C := by
  classical
  obtain ⟨χ₁, M₁, hχ₁, hM₁, hM₁d⟩ := stage1_succ (X := AType (col3 A B C))
    (Y := BType (col3 A B C)) hA4 card_classA (by rw [card_classB, hB])
  exact master_of_stage1 hadm hC (by omega) (by omega) (by omega) hρ6 h76 χ₁ M₁ hχ₁ hM₁ hM₁d
    (fun v => by omega)

end CDRBicolour.Master
