/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.Shift
public import CDRBicolour.Absorption.Refined.GenSeed

/-!
# Octahedral expansion of wrong-parity triangles (refined H1, item 2b)

`rv j T = (Σ_{v ∈ T} v mod 6 + 6 − 3j) mod 6`; `T` is *right* when `rv j T < 3`.  A wrong
bicoloured triangle `T = {x,y,z}` is replaced by the seven other faces of the octahedron on
`x, y, z, τx, τy, τz` (shift `δ = 5` if `rv = 3`, `δ = 1` otherwise; a good shift from
`exists_good_shift`).  The operator

`psi1 c T' = [T' right] c T' + Σ_{T wrong} c T · coefT T T'`

keeps the incidence (`Minc_psi1`), only produces wrong triangles of value `5`
(`psi1_zero_34`), and `psi1 ∘ psi1` produces only right triangles (`psi2_zero`).  Each output
value is bounded by `32929` times the input bound (`abs_psi1_le`): a triangle `T'` is a face of
the expansion of at most `4704` triangles (`card_coef_ne`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Refined

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {a b c : ℕ}

/-- The value of a triangle in parity class `j`. -/
def rv (j : ℕ) (T : Finset (Fin (a + b + c))) : ℕ := ((∑ v ∈ T, v.val % 6) + 6 - 3 * j) % 6

/-- The shift used for a wrong triangle. -/
def del (j : ℕ) (T : Finset (Fin (a + b + c))) : ℕ := if rv j T = 3 then 5 else 1

theorem del_cases (j : ℕ) (T : Finset (Fin (a + b + c))) :
    (rv j T = 3 ∧ del j T = 5) ∨ (rv j T ≠ 3 ∧ del j T = 1) := by
  unfold del; split_ifs with h <;> simp [h]

/-- Expansion data: an ordering of `T` and a good shift. -/
def ExpData (j : ℕ) (T : Finset (Fin (a + b + c)))
    (q : (Fin (a + b + c) × Fin (a + b + c) × Fin (a + b + c)) × ℕ × ℕ) : Prop :=
  q.1.1 ≠ q.1.2.1 ∧ q.1.1 ≠ q.1.2.2 ∧ q.1.2.1 ≠ q.1.2.2 ∧ T = {q.1.1, q.1.2.1, q.1.2.2} ∧
    q.2.1 < 4 ∧ q.2.2 < 7 ∧ GoodShift a b c (del j T) q.2.1 q.2.2 q.1.1 q.1.2.1 q.1.2.2

/-- Point mass at a triangle. -/
def dlt (S : Finset (Fin (a + b + c))) : Finset (Fin (a + b + c)) → ℝ :=
  fun T => if T = S then 1 else 0

/-- The seven other faces of the octahedron, with signs. -/
def octC (x y z x' y' z' : Fin (a + b + c)) : Finset (Fin (a + b + c)) → ℝ :=
  dlt {x, y, z'} + dlt {x, y', z} + dlt {x', y, z} + dlt {x', y', z'} - dlt {x, y', z'} -
    dlt {x', y, z'} - dlt {x', y', z}

open Classical in
/-- The expansion of a triangle. -/
def coefT (j : ℕ) (T : Finset (Fin (a + b + c))) : Finset (Fin (a + b + c)) → ℝ :=
  if h : ∃ q, ExpData j T q then
    octC (Classical.choose h).1.1 (Classical.choose h).1.2.1 (Classical.choose h).1.2.2
      (tau a b c (del j T) (Classical.choose h).2.1 (Classical.choose h).2.2
        (Classical.choose h).1.1)
      (tau a b c (del j T) (Classical.choose h).2.1 (Classical.choose h).2.2
        (Classical.choose h).1.2.1)
      (tau a b c (del j T) (Classical.choose h).2.1 (Classical.choose h).2.2
        (Classical.choose h).1.2.2)
  else 0

/-- Wrong triangles of the complete host. -/
abbrev wrongT (a b c : ℕ) (j : ℕ) : Finset (Finset (Fin (a + b + c))) :=
  (tri (col3 a b c)).filter fun T => 3 ≤ rv j T

/-- The expansion operator. -/
def psi1 (j : ℕ) : (Finset (Fin (a + b + c)) → ℝ) →ₗ[ℝ] (Finset (Fin (a + b + c)) → ℝ) where
  toFun cf T' := (if rv j T' < 3 then cf T' else 0) + ∑ T ∈ wrongT a b c j, cf T * coefT j T T'
  map_add' cf cf' := by
    ext T'; simp only [Pi.add_apply, add_mul, sum_add_distrib]; split_ifs <;> ring
  map_smul' r cf := by
    ext T'; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, mul_sum]; simp only [mul_assoc]; split_ifs <;> simp

/-! ### Basic facts -/

theorem sum3 (g : Fin (a + b + c) → ℕ) {x y z : Fin (a + b + c)} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ∑ v ∈ ({x, y, z} : Finset (Fin (a + b + c))), g v = g x + g y + g z := by
  rw [sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton, add_assoc]

theorem cols_of_tri {x y z : Fin (a + b + c)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hT : ({x, y, z} : Finset (Fin (a + b + c))) ∈ tri (col3 a b c)) :
    ({col3 a b c x, col3 a b c y, col3 a b c z} : Multiset (Fin 3)) ∈ cdrF := by
  have := (mem_tri.mp hT).2.2
  rwa [val_map_triple (col3 a b c) hxy (Ne.symm hxz) (Ne.symm hyz)] at this

theorem tri_face {x y z p q r : Fin (a + b + c)} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (cp : col3 a b c p = col3 a b c x) (cq : col3 a b c q = col3 a b c y)
    (cr : col3 a b c r = col3 a b c z)
    (hF : ({col3 a b c x, col3 a b c y, col3 a b c z} : Multiset (Fin 3)) ∈ cdrF) :
    ({p, q, r} : Finset (Fin (a + b + c))) ∈ tri (col3 a b c) :=
  mem_tri.mpr (isAllowed_triple (col3 a b c) hpq hpr hqr (by rw [cp, cq, cr]; exact hF))

theorem exists_expData (hbig : BigCls a b c) (j : ℕ) {T : Finset (Fin (a + b + c))}
    (hT : T ∈ tri (col3 a b c)) : ∃ q, ExpData j T q := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 (mem_tri.mp hT).1
  have hd : del j {x, y, z} < 6 ∧ 0 < del j {x, y, z} := by
    rcases del_cases j {x, y, z} with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> omega
  obtain ⟨f, hf, k, hk, hg⟩ := exists_good_shift hbig hd.1 hd.2 hxy hxz hyz
  exact ⟨((x, y, z), f, k), hxy, hxz, hyz, rfl, hf, hk, hg⟩

/-- Unfolded expansion of a triangle of the complete host. -/
theorem coefT_spec (hbig : BigCls a b c) (j : ℕ) {T : Finset (Fin (a + b + c))}
    (hT : T ∈ tri (col3 a b c)) :
    ∃ x y z : Fin (a + b + c), ∃ f k : ℕ, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ T = {x, y, z} ∧ f < 4 ∧
      k < 7 ∧ GoodShift a b c (del j T) f k x y z ∧
      coefT j T = octC x y z (tau a b c (del j T) f k x) (tau a b c (del j T) f k y)
        (tau a b c (del j T) f k z) := by
  have h := exists_expData hbig j hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Classical.choose_spec h
  refine ⟨_, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  unfold coefT
  rw [dif_pos h]

theorem del_lt (j : ℕ) (T : Finset (Fin (a + b + c))) : del j T < 6 ∧ 0 < del j T := by
  rcases del_cases j T with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> omega

/-! ### Incidence -/

theorem Minc_dlt {S : Finset (Fin (a + b + c))} (hS : S ∈ tri (col3 a b c)) (e : E0 (Fin (a + b + c))) :
    Minc (col3 a b c) (dlt S) e = if e.1 ∈ triEdges S then 1 else 0 := by
  simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk, dlt]
  rw [sum_ite_eq']
  simp only [mem_filter, hS, true_and]

theorem ind_apply (J : Finset (Sym2 (Fin (a + b + c)))) (e : Sym2 (Fin (a + b + c))) :
    ((ind J e : ℤ) : ℝ) = if e ∈ J then 1 else 0 := by
  unfold ind; split_ifs <;> simp

/-- The octahedral combination covers exactly the edges of `xyz`. -/
theorem Minc_octC (hbig : BigCls a b c) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    {x y z : Fin (a + b + c)} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hg : GoodShift a b c δ f k x y z)
    (hT : ({x, y, z} : Finset (Fin (a + b + c))) ∈ tri (col3 a b c)) (e : E0 (Fin (a + b + c))) :
    Minc (col3 a b c) (octC x y z (tau a b c δ f k x) (tau a b c δ f k y) (tau a b c δ f k z)) e =
      if e.1 ∈ triEdges ({x, y, z} : Finset (Fin (a + b + c))) then 1 else 0 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  set x' := tau a b c δ f k x
  set y' := tau a b c δ f k y
  set z' := tau a b c δ f k z
  have hF := cols_of_tri hxy hxz hyz hT
  have cx := tau_col hbig hδ hf hk x
  have cy := tau_col hbig hδ hf hk y
  have cz := tau_col hbig hδ hf hk z
  have t1 := tri_face (x := x) (y := y) (z := z) hxy (Ne.symm g8) (Ne.symm g9) rfl rfl cz hF
  have t2 := tri_face (x := x) (y := y) (z := z) (Ne.symm g6) hxz g7 rfl cy rfl hF
  have t3 := tri_face (x := x) (y := y) (z := z) g4 g5 hyz cx rfl rfl hF
  have t4 := tri_face (x := x) (y := y) (z := z) g1 g2 g3 cx cy cz hF
  have t5 := tri_face (x := x) (y := y) (z := z) (Ne.symm g6) (Ne.symm g8) g3 rfl cy cz hF
  have t6 := tri_face (x := x) (y := y) (z := z) g4 g2 (Ne.symm g9) cx rfl cz hF
  have t7 := tri_face (x := x) (y := y) (z := z) g1 g5 g7 cx cy rfl hF
  have hoct := congrFun (oct_ind hxy hxz hyz g4 g5 (Ne.symm g6) g7 g1 (Ne.symm g8)
    (Ne.symm g9) g2 g3) e.1
  simp only [Pi.add_apply, Pi.sub_apply] at hoct
  have hR := congrArg (fun t : ℤ => (t : ℝ)) hoct
  simp only [Int.cast_add, Int.cast_sub, ind_apply] at hR
  unfold octC
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, Minc_dlt t1, Minc_dlt t2, Minc_dlt t3,
    Minc_dlt t4, Minc_dlt t5, Minc_dlt t6, Minc_dlt t7]
  rw [hR]

theorem Minc_coefT (hbig : BigCls a b c) (j : ℕ) {T : Finset (Fin (a + b + c))}
    (hT : T ∈ tri (col3 a b c)) (e : E0 (Fin (a + b + c))) :
    Minc (col3 a b c) (coefT j T) e = if e.1 ∈ triEdges T then 1 else 0 := by
  obtain ⟨x, y, z, f, k, hxy, hxz, hyz, hTe, hf, hk, hg, hc⟩ := coefT_spec hbig j hT
  rw [hc]
  have hT' := hT
  rw [hTe] at hT' ⊢
  exact Minc_octC hbig (del_lt j _).1 hf hk hxy hxz hyz (hTe ▸ hg) hT' e

/-- **The expansion keeps the incidence.** -/
theorem Minc_psi1 (hbig : BigCls a b c) (j : ℕ) (cf : Finset (Fin (a + b + c)) → ℝ) :
    Minc (col3 a b c) (psi1 j cf) = Minc (col3 a b c) cf := by
  ext e
  simp only [Minc, psi1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_add_distrib, sum_comm]
  have h2 : ∀ T ∈ wrongT a b c j,
      ∑ T' ∈ (tri (col3 a b c)).filter (fun T' => e.1 ∈ triEdges T'), cf T * coefT j T T' =
        if e.1 ∈ triEdges T then cf T else 0 := by
    intro T hT
    rw [← mul_sum]
    have := Minc_coefT hbig j (mem_filter.mp hT).1 e
    simp only [Minc, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this]; split_ifs <;> ring
  rw [sum_congr rfl h2, ← sum_filter, ← sum_filter, filter_filter, filter_filter]
  rw [← sum_filter_add_sum_filter_not ((tri (col3 a b c)).filter fun T => e.1 ∈ triEdges T)
    (fun T => rv j T < 3)]
  congr 1
  · rw [filter_filter]
  · refine sum_congr ?_ fun _ _ => rfl
    ext T; simp only [mem_filter, not_lt]; tauto

/-! ### Values of the faces -/

theorem rv_face (hbig : BigCls a b c) (j : ℕ) {δ f k : ℕ} (hδ : δ < 6) (hf : f < 4) (hk : k < 7)
    {p q r : Fin (a + b + c)} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (s : ℕ)
    (hs : p.val % 6 + q.val % 6 + r.val % 6 = s) :
    rv j ({p, q, r} : Finset (Fin (a + b + c))) = (s + 6 - 3 * j) % 6 := by
  unfold rv; rw [sum3 (fun v => v.val % 6) hpq hpr hqr, hs]

/-- Faces of a wrong triangle never have value `3` or `4`; for `rv ∈ {3, 5}` they are right. -/
theorem face_values (hbig : BigCls a b c) (j : ℕ) (hj : j < 2) {T : Finset (Fin (a + b + c))}
    (hT : T ∈ wrongT a b c j) {T' : Finset (Fin (a + b + c))} (hc : coefT j T T' ≠ 0) :
    rv j T' < 3 ∨ (rv j T' = 5 ∧ rv j T = 4) := by
  obtain ⟨hTt, hw⟩ := mem_filter.mp hT
  obtain ⟨x, y, z, f, k, hxy, hxz, hyz, hTe, hf, hk, hg, hco⟩ := coefT_spec hbig j hTt
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  have hd := del_lt j T
  have mx := tau_mod hbig hd.1 hf hk x
  have my := tau_mod hbig hd.1 hf hk y
  have mz := tau_mod hbig hd.1 hf hk z
  have hrT : rv j T = ((x.val % 6 + y.val % 6 + z.val % 6) + 6 - 3 * j) % 6 := by
    rw [hTe]; unfold rv; rw [sum3 (fun v => v.val % 6) hxy hxz hyz]
  have hdc := del_cases j T
  rw [hco] at hc
  unfold octC dlt at hc
  simp only [Pi.add_apply, Pi.sub_apply] at hc
  by_cases e1 : T' = {x, y, tau a b c (del j T) f k z}
  · rw [e1, rv_face hbig j hd.1 hf hk hxy (Ne.symm g8) (Ne.symm g9) _ rfl]; omega
  by_cases e2 : T' = {x, tau a b c (del j T) f k y, z}
  · rw [e2, rv_face hbig j hd.1 hf hk (Ne.symm g6) hxz g7 _ rfl]; omega
  by_cases e3 : T' = {tau a b c (del j T) f k x, y, z}
  · rw [e3, rv_face hbig j hd.1 hf hk g4 g5 hyz _ rfl]; omega
  by_cases e4 : T' = {tau a b c (del j T) f k x, tau a b c (del j T) f k y, tau a b c (del j T) f k z}
  · rw [e4, rv_face hbig j hd.1 hf hk g1 g2 g3 _ rfl]; omega
  by_cases e5 : T' = {x, tau a b c (del j T) f k y, tau a b c (del j T) f k z}
  · rw [e5, rv_face hbig j hd.1 hf hk (Ne.symm g6) (Ne.symm g8) g3 _ rfl]; omega
  by_cases e6 : T' = {tau a b c (del j T) f k x, y, tau a b c (del j T) f k z}
  · rw [e6, rv_face hbig j hd.1 hf hk g4 g2 (Ne.symm g9) _ rfl]; omega
  by_cases e7 : T' = {tau a b c (del j T) f k x, tau a b c (del j T) f k y, z}
  · rw [e7, rv_face hbig j hd.1 hf hk g1 g5 g7 _ rfl]; omega
  exfalso; apply hc
  simp only [e1, e2, e3, e4, e5, e6, e7, if_false]; ring

/-- Outputs never have value `3` or `4`. -/
theorem psi1_zero_34 (hbig : BigCls a b c) (j : ℕ) (hj : j < 2) (cf : Finset (Fin (a + b + c)) → ℝ)
    {T' : Finset (Fin (a + b + c))} (h : rv j T' = 3 ∨ rv j T' = 4) : psi1 j cf T' = 0 := by
  simp only [psi1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_neg (by omega), zero_add]
  refine sum_eq_zero fun T hT => ?_
  by_cases hc : coefT j T T' = 0
  · rw [hc, mul_zero]
  · rcases face_values hbig j hj hT hc with h1 | ⟨h1, -⟩ <;> omega

/-- **After two expansions only right triangles carry weight.** -/
theorem psi2_zero (hbig : BigCls a b c) (j : ℕ) (hj : j < 2) (cf : Finset (Fin (a + b + c)) → ℝ)
    {T' : Finset (Fin (a + b + c))} (h : 3 ≤ rv j T') : psi1 j (psi1 j cf) T' = 0 := by
  simp only [psi1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_neg (by omega), zero_add]
  refine sum_eq_zero fun T hT => ?_
  have h34 : ¬ (rv j T = 3 ∨ rv j T = 4) → coefT j T T' = 0 := by
    intro hn
    by_contra hc
    rcases face_values hbig j hj hT hc with h1 | ⟨-, h1⟩ <;> omega
  by_cases hT34 : rv j T = 3 ∨ rv j T = 4
  · have := psi1_zero_34 hbig j hj cf hT34
    simp only [psi1, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, zero_mul]
  · rw [h34 hT34, mul_zero]

/-! ### The bound -/

/-- Index set of the shifts. -/
def shIdx : Finset (ℕ × ℕ × ℕ) := ({1, 5} : Finset ℕ) ×ˢ range 4 ×ˢ range 7

/-- Points of `T'` and their preimages under a shift. -/
def preU (p : ℕ × ℕ × ℕ) (T' : Finset (Fin (a + b + c))) : Finset (Fin (a + b + c)) :=
  T' ∪ T'.biUnion fun s => univ.filter fun v => tau a b c p.1 p.2.1 p.2.2 v = s

/-- Candidates whose expansion can contain `T'`. -/
def cand (T' : Finset (Fin (a + b + c))) : Finset (Finset (Fin (a + b + c))) :=
  shIdx.biUnion fun p => (preU p T').powersetCard 3

theorem card_preU (hbig : BigCls a b c) {p : ℕ × ℕ × ℕ} (hp : p ∈ shIdx)
    (T' : Finset (Fin (a + b + c))) : #(preU p T') ≤ 3 * #T' := by
  simp only [shIdx, mem_product, mem_insert, mem_singleton, mem_range] at hp
  obtain ⟨hδ, hf, hk⟩ := hp
  have hδ6 : p.1 < 6 := by omega
  calc #(preU p T') ≤ #T' + #(T'.biUnion fun s => univ.filter fun v =>
        tau a b c p.1 p.2.1 p.2.2 v = s) := card_union_le _ _
    _ ≤ #T' + ∑ s ∈ T', #(univ.filter fun v => tau a b c p.1 p.2.1 p.2.2 v = s) := by
        gcongr; exact card_biUnion_le
    _ ≤ #T' + ∑ _s ∈ T', 2 := by gcongr with s; exact card_fibre hbig hδ6 hf hk s
    _ = 3 * #T' := by rw [sum_const, smul_eq_mul]; ring

theorem card_cand (hbig : BigCls a b c) {T' : Finset (Fin (a + b + c))} (h3 : #T' = 3) :
    #(cand T') ≤ 4704 := by
  calc #(cand T') ≤ ∑ p ∈ shIdx, #((preU p T').powersetCard 3) := card_biUnion_le
    _ ≤ ∑ _p ∈ shIdx, 84 := by
        gcongr with p hp
        rw [card_powersetCard]
        calc (#(preU p T')).choose 3 ≤ (9 : ℕ).choose 3 :=
              Nat.choose_le_choose 3 (by have := card_preU hbig hp T'; omega)
          _ = 84 := by decide
    _ = 4704 := by simp [shIdx]

theorem mem_cand (hbig : BigCls a b c) (j : ℕ) {T T' : Finset (Fin (a + b + c))}
    (hT : T ∈ tri (col3 a b c)) (hc : coefT j T T' ≠ 0) : T ∈ cand T' ∧ #T' = 3 := by
  obtain ⟨x, y, z, f, k, hxy, hxz, hyz, hTe, hf, hk, hg, hco⟩ := coefT_spec hbig j hT
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  set τ := tau a b c (del j T) f k
  have hp : (del j T, f, k) ∈ shIdx := by
    simp only [shIdx, mem_product, mem_insert, mem_singleton, mem_range]
    rcases del_cases j T with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [hf, hk]
  -- every point of `T` or its shift lies in `T'`
  have key : T' = {x, y, τ z} ∨ T' = {x, τ y, z} ∨ T' = {τ x, y, z} ∨ T' = {τ x, τ y, τ z} ∨
      T' = {x, τ y, τ z} ∨ T' = {τ x, y, τ z} ∨ T' = {τ x, τ y, z} := by
    rw [hco] at hc
    unfold octC dlt at hc
    simp only [Pi.add_apply, Pi.sub_apply] at hc
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hn
    apply hc
    simp only [n1, n2, n3, n4, n5, n6, n7, if_false]; ring
  have hsub : ∀ v ∈ ({x, y, z} : Finset (Fin (a + b + c))), v ∈ T' ∨ τ v ∈ T' := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases key with h | h | h | h | h | h | h <;> rw [h] <;> rcases hv with rfl | rfl | rfl <;>
      simp
  have h3 : #T' = 3 := by
    rcases key with h | h | h | h | h | h | h <;> rw [h]
    · exact card_eq_three.2 ⟨_, _, _, hxy, Ne.symm g8, Ne.symm g9, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, Ne.symm g6, hxz, g7, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, g4, g5, hyz, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, g1, g2, g3, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, Ne.symm g6, Ne.symm g8, g3, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, g4, g2, Ne.symm g9, rfl⟩
    · exact card_eq_three.2 ⟨_, _, _, g1, g5, g7, rfl⟩
  refine ⟨?_, h3⟩
  unfold cand
  refine mem_biUnion.2 ⟨_, hp, mem_powersetCard.2 ⟨fun v hv => ?_, ?_⟩⟩
  · rw [hTe] at hv
    rcases hsub v hv with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_biUnion.2 ⟨τ v, h, by simp [τ]⟩)
  · rw [hTe]; exact card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩

theorem abs_coefT_le (j : ℕ) (T T' : Finset (Fin (a + b + c))) : |coefT j T T'| ≤ 7 := by
  unfold coefT
  split_ifs
  · unfold octC dlt
    simp only [Pi.add_apply, Pi.sub_apply]
    split_ifs <;> norm_num
  · simp

/-- **Bound for the expansion.** -/
theorem abs_psi1_le (hbig : BigCls a b c) (j : ℕ) (cf : Finset (Fin (a + b + c)) → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hc : ∀ T, |cf T| ≤ r) (T' : Finset (Fin (a + b + c))) :
    |psi1 j cf T'| ≤ 32929 * r := by
  simp only [psi1, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : |(if rv j T' < 3 then cf T' else 0)| ≤ r := by
    split_ifs
    · exact hc T'
    · simpa using hr
  have hfilt : ∑ T ∈ wrongT a b c j, cf T * coefT j T T' =
      ∑ T ∈ (wrongT a b c j).filter (fun T => coefT j T T' ≠ 0), cf T * coefT j T T' :=
    (sum_filter_of_ne fun T _ h => right_ne_zero_of_mul h).symm
  have h2 : |∑ T ∈ wrongT a b c j, cf T * coefT j T T'| ≤ 32928 * r := by
    rw [hfilt]
    by_cases hne : ((wrongT a b c j).filter fun T => coefT j T T' ≠ 0).Nonempty
    · obtain ⟨T₀, hT₀⟩ := hne
      have h3 := (mem_cand hbig j (mem_filter.mp (mem_filter.mp hT₀).1).1
        (mem_filter.mp hT₀).2).2
      have hsub : ((wrongT a b c j).filter fun T => coefT j T T' ≠ 0) ⊆ cand T' := by
        intro T hT
        exact (mem_cand hbig j (mem_filter.mp (mem_filter.mp hT).1).1 (mem_filter.mp hT).2).1
      have hcard := (card_le_card hsub).trans (card_cand hbig h3)
      calc _ ≤ ∑ T ∈ (wrongT a b c j).filter (fun T => coefT j T T' ≠ 0),
            |cf T * coefT j T T'| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _T ∈ (wrongT a b c j).filter (fun T => coefT j T T' ≠ 0), r * 7 := by
            gcongr with T
            rw [abs_mul]
            exact mul_le_mul (hc T) (abs_coefT_le j T T') (abs_nonneg _) hr
        _ = #((wrongT a b c j).filter fun T => coefT j T T' ≠ 0) * (r * 7) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ 4704 * (r * 7) := by
            gcongr; exact_mod_cast hcard
        _ = 32928 * r := by ring
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty, abs_zero]; positivity
  calc _ ≤ |(if rv j T' < 3 then cf T' else 0)| +
        |∑ T ∈ wrongT a b c j, cf T * coefT j T T'| := abs_add_le _ _
    _ ≤ r + 32928 * r := add_le_add h1 h2
    _ = 32929 * r := by ring

end CDRBicolour.Absorption.Refined
