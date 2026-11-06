/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.SeedFamily
public import CDRBicolour.Extensions.BlockTypes

/-!
# `AAC` blocks: seed total and block count

* `card_aac`: the CDR host has exactly `C(a,2) · c` triangles of type `AAC`;
* `seed_aac_total`: the seed `wtS s` puts total weight `(1/2 - σ_A - s) · C(a,2)` on them;
* `sts_of_decomposition`: an allowed decomposition `D` is a strictly bicoloured STS with
  blocks `D`, and its `typeCount … 0 2` (blocks `AAC`) counts the `AAC` triangles of `D`.
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.BlockTypes

variable {a b c : ℕ}

/-- The label pattern `AAC`. -/
def aac : Multiset (Fin 3) := {0, 0, 2}

theorem map_triple {V : Type*} [DecidableEq V] [Fintype V] (f : V → Fin 3) {p q r : V} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    ({p, q, r} : Finset V).val.map f = {f p, f q, f r} := by
  rw [insert_val_of_notMem (by simp [hpq, hpr]), insert_val_of_notMem (by simp [hqr])]
  simp

theorem fin3_aac : ∀ x y z : Fin 3,
    (((if x = 0 then 1 else 0) + (if y = 0 then 1 else 0) + (if z = 0 then 1 else 0) : ℕ) = 2 ∧
      ((if x = 2 then 1 else 0) + (if y = 2 then 1 else 0) + (if z = 2 then 1 else 0) : ℕ) = 1) ↔
      ({x, y, z} : Multiset (Fin 3)) = aac := by
  decide

/-- For a 3-set, "two points of colour `0`, one of colour `2`" is the pattern `AAC`. -/
theorem cnt_iff_aac {V : Type*} [DecidableEq V] [Fintype V] (f : V → Fin 3) {B : Finset V}
    (hB : B.card = 3) : (cnt f 0 B = 2 ∧ cnt f 2 B = 1) ↔ B.val.map f = aac := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp hB
  rw [cnt_triple f 0 hpq hpr hqr, cnt_triple f 2 hpq hpr hqr, map_triple f hpq hpr hqr]
  exact fin3_aac _ _ _

theorem aac_mem_cdrF : aac ∈ cdrF := by
  refine ⟨rfl, ?_⟩
  decide

/-- The `AAC` triangles of the host, as pairs in class `A` plus a point of class `C`. -/
theorem card_aac :
    #(univ.filter fun T : Finset (Fin (a + b + c)) =>
        T.card = 3 ∧ T.val.map (col3 a b c) = aac) = a.choose 2 * c := by
  classical
  set A := univ.filter fun v : Fin (a + b + c) => col3 a b c v = 0
  set C := univ.filter fun v : Fin (a + b + c) => col3 a b c v = 2
  have hA : #A = a := by simpa using card_class a b c 0
  have hC : #C = c := by simpa using card_class a b c 2
  have hinj : Set.InjOn (fun p : Finset (Fin (a + b + c)) × Fin (a + b + c) => insert p.2 p.1)
      (A.powersetCard 2 ×ˢ C : Finset _) := by
    rintro ⟨P, z⟩ hp ⟨P', z'⟩ hp' heq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard, mem_filter, mem_univ,
      true_and, A, C] at hp hp'
    simp only at heq
    have hzP : z ∉ P := fun h => by have := (mem_filter.mp (hp.1.1 h)).2; rw [hp.2] at this; simp at this
    have hzP' : z' ∉ P' := fun h => by have := (mem_filter.mp (hp'.1.1 h)).2; rw [hp'.2] at this; simp at this
    have hz : z = z' := by
      have hz' : z' ∈ insert z P := heq ▸ mem_insert_self z' P'
      rcases mem_insert.mp hz' with h | h
      · exact h.symm
      · have := (mem_filter.mp (hp.1.1 h)).2; rw [hp'.2] at this; simp at this
    subst hz
    refine Prod.ext ?_ rfl
    simp only
    rw [← erase_insert hzP, ← erase_insert hzP', heq]
  have hset : (univ.filter fun T : Finset (Fin (a + b + c)) =>
      T.card = 3 ∧ T.val.map (col3 a b c) = aac) =
      (A.powersetCard 2 ×ˢ C).image (fun p => insert p.2 p.1) := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_product, mem_powersetCard, Prod.exists]
    constructor
    · rintro ⟨hT3, hTm⟩
      have hc := (cnt_iff_aac (col3 a b c) hT3).mpr hTm
      obtain ⟨z, hz⟩ := card_eq_one.mp hc.2
      have hzT : z ∈ T ∧ col3 a b c z = 2 := mem_filter.mp (hz ▸ mem_singleton_self z)
      refine ⟨T.filter fun v => col3 a b c v = 0, z, ⟨⟨fun v hv => ?_, hc.1⟩, ?_⟩, ?_⟩
      · exact mem_filter.mpr ⟨mem_univ v, (mem_filter.mp hv).2⟩
      · exact mem_filter.mpr ⟨mem_univ z, hzT.2⟩
      · ext v
        simp only [mem_insert, mem_filter]
        constructor
        · rintro (rfl | ⟨hv, _⟩)
          · exact hzT.1
          · exact hv
        · intro hv
          by_cases h0 : col3 a b c v = 0
          · exact Or.inr ⟨hv, h0⟩
          · left
            by_cases h2 : col3 a b c v = 2
            · have : v ∈ T.filter (fun v => col3 a b c v = 2) := mem_filter.mpr ⟨hv, h2⟩
              rw [hz] at this
              exact mem_singleton.mp this
            · exfalso
              -- a point of colour 1 would make the pattern different from `AAC`
              have h1 : col3 a b c v = 1 := by
                generalize col3 a b c v = k at h0 h2
                fin_cases k <;> simp_all
              have : (1 : Fin 3) ∈ T.val.map (col3 a b c) := Multiset.mem_map.mpr ⟨v, hv, h1⟩
              rw [hTm] at this
              exact absurd this (by decide)
    · rintro ⟨P, z, ⟨⟨hPA, hP2⟩, hzC⟩, rfl⟩
      have hz2 : col3 a b c z = 2 := (mem_filter.mp hzC).2
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hP2
      have hx0 : col3 a b c x = 0 := (mem_filter.mp (hPA (by simp))).2
      have hy0 : col3 a b c y = 0 := (mem_filter.mp (hPA (by simp))).2
      have hzx : z ≠ x := fun h => by rw [h, hx0] at hz2; simp at hz2
      have hzy : z ≠ y := fun h => by rw [h, hy0] at hz2; simp at hz2
      refine ⟨card_eq_three.mpr ⟨z, x, y, hzx, hzy, hxy, rfl⟩, ?_⟩
      rw [map_triple _ hzx hzy hxy, hz2, hx0, hy0]
      decide
  rw [hset, card_image_of_injOn hinj, card_product, card_powersetCard, hA, hC]

/-- The seed puts total weight `(1/2 - σ_A - s) · C(a,2)` on the `AAC` triangles. -/
theorem seed_aac_total (h : AdmissibleProfile a b c) (s : ℝ) :
    ∑ Q ∈ allowed (cdrHost a b c) cdrF,
        wtS a b c s (Q.val.map (col3 a b c)) *
          (if Q.val.map (col3 a b c) = aac then 1 else 0) =
      (1 / 2 - sigA a c - s) * (a.choose 2 : ℝ) := by
  classical
  have hc0 : (c : ℝ) ≠ 0 := by have := h.2.2.1; positivity
  have hw : wtS a b c s aac = (1 / 2 - sigA a c - s) / c := by
    simp [wtS, wt, dir, aac]; ring
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have hfil : (allowed (cdrHost a b c) cdrF).filter (fun Q => Q.val.map (col3 a b c) = aac) =
      univ.filter fun T : Finset (Fin (a + b + c)) =>
        T.card = 3 ∧ T.val.map (col3 a b c) = aac := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTa, hm⟩ := mem_filter.mp hT
      have hA : IsAllowed (cdrHost a b c) cdrF T := by
        unfold allowed at hTa; exact (mem_filter.mp hTa).2
      exact mem_filter.mpr ⟨mem_univ _, hA.1, hm⟩
    · intro hT
      obtain ⟨-, h3, hm⟩ := mem_filter.mp hT
      have hA : IsAllowed (cdrHost a b c) cdrF T :=
        ⟨h3, fun x _ y _ hxy => hxy, hm ▸ aac_mem_cdrF⟩
      refine mem_filter.mpr ⟨?_, hm⟩
      unfold allowed
      exact mem_filter.mpr ⟨mem_univ _, hA⟩
  rw [hfil, sum_congr rfl (fun Q hQ => by rw [(mem_filter.mp hQ).2.2, hw]), sum_const,
    card_aac, nsmul_eq_mul]
  push_cast
  field_simp

/-- An allowed decomposition gives a strictly bicoloured STS with blocks `D`. -/
theorem sts_of_decomposition (D : Finset (Finset (Fin (a + b + c))))
    (hD : IsDecomposition (cdrHost a b c) cdrF (edges (cdrHost a b c)) D) :
    ∃ S : STS (Fin (a + b + c)), S.blocks = D ∧ IsStrictBicolouring S (col3 a b c) ∧
      classSize (col3 a b c) 0 = a ∧ classSize (col3 a b c) 1 = b ∧
      classSize (col3 a b c) 2 = c := by
  classical
  obtain ⟨hall, hdisj, hcov⟩ := hD
  have hmem : ∀ T ∈ D, ∀ x y, x ≠ y → (s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T) := by
    intro T _ x y hxy
    simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, hxy]
  refine ⟨⟨D, fun T hT => (hall T hT).1, fun x y hxy => ?_⟩, rfl, ?_, ?_, ?_, ?_⟩
  · have he : s(x, y) ∈ edges (cdrHost a b c) := by
      simp [edges, cdrHost, hxy]
    rw [← hcov] at he
    simp only [Finset.mem_biUnion] at he
    obtain ⟨T, hT, hxyT⟩ := he
    refine ⟨T, ⟨hT, (hmem T hT x y hxy).1 hxyT⟩, ?_⟩
    rintro T' ⟨hT', hx', hy'⟩
    by_contra hne
    have := hdisj hT' hT hne
    exact disjoint_left.1 this ((hmem T' hT' x y hxy).2 ⟨hx', hy'⟩) hxyT
  · intro T hT
    exact (hall T hT).2.2.2
  · rw [classSize, ← Fintype.card_subtype]; exact card_classA
  · rw [classSize, ← Fintype.card_subtype]; exact card_classB
  · rw [classSize, ← Fintype.card_subtype]; exact card_classC

/-- The `AAC` block count of an STS with blocks `D` counts the `AAC` triangles of `D`. -/
theorem typeCount_aac (S : STS (Fin (a + b + c))) :
    (typeCount S (col3 a b c) 0 2 : ℝ) =
      ∑ Q ∈ S.blocks, (if Q.val.map (col3 a b c) = aac then 1 else 0) := by
  rw [typeCount, sum_boole]
  congr 2
  exact filter_congr fun B hB => cnt_iff_aac _ (S.card_eq_three B hB)

end CDRBicolour.Absorption
