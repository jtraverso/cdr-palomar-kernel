/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Extremes.Lattice5
public import CDRBicolour.Absorption.Refined.GenSeed
public import CDRBicolour.Absorption.BRIFinal

/-!
# A bounded right inverse for the five-type host (item 3, extremes)

Every `AAC` triangle `T = {u,v,w}` is replaced by the average, over the auxiliary points
`b₂ ≠ b₃ ∈ B` and `c₅ ≠ c₆ ∈ C \ {w}`, of half the `I2` combination (17 non-`AAC` triangles
with incidence `2·𝟏_T`).  The operator

`Ψ c T' = [T' ∈ F5] c T' + Σ_{T AAC} c T / (2 g_T) · Σ_{t ∈ goods T} gad t T'`

keeps the incidence (`Minc_Psi`), and `|Ψ c| ≤ (1 + 9·343·n⁴/M)·max|c|` when every `AAC`
triangle has at least `M` placements (`abs_Psi_le`): a triangle `T'` lies in the image of at most
`343 n⁴` placements (`card_cover_le`).  Composed with the bounded inverse of the full CDR host it
gives a bounded inverse of the five-type host (`bri5`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Extremes

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Exact
  CDRBicolour.Absorption.Refined

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin 3)

/-- The image of the `I2` combination under a placement `t`. -/
def gad (t : Fin 7 → V) (T' : Finset V) : ℝ :=
  (I2L.map fun p => (p.1 : ℝ) * if T' = p.2.image t then 1 else 0).sum

/-- Placements of the `I2` gadget on an `AAC` triangle `T`. -/
def goods (T : Finset V) : Finset (Fin 7 → V) :=
  univ.filter fun t => Function.Injective t ∧ (∀ i, lab (t i) = mlab 2 2 i) ∧
    ({t 0, t 1, t 4} : Finset V) = T

/-- `AAC` triangles of the complete host. -/
def aacs : Finset (Finset V) := (triG lab cdrF).filter fun T => T.val.map lab = aac

/-- The replacement operator. -/
def Psi : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c T' := (if T' ∈ triG lab F5 then c T' else 0) +
    ∑ T ∈ aacs lab, c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T'
  map_add' c c' := by
    funext T'
    simp only [Pi.add_apply]
    rw [show (∑ T ∈ aacs lab, (c T + c' T) / (2 * (goods lab T).card) *
        ∑ t ∈ goods lab T, gad t T') = (∑ T ∈ aacs lab, c T / (2 * (goods lab T).card) *
        ∑ t ∈ goods lab T, gad t T') + ∑ T ∈ aacs lab, c' T / (2 * (goods lab T).card) *
        ∑ t ∈ goods lab T, gad t T' by rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring]
    split_ifs <;> ring
  map_smul' r c := by
    funext T'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, mul_sum]
    congr 1
    · split_ifs <;> ring
    · exact sum_congr rfl fun _ _ => by ring

/-! ### Placements -/

theorem goods_spec {T : Finset V} {t : Fin 7 → V} (ht : t ∈ goods lab T) :
    Function.Injective t ∧ (∀ i, lab (t i) = mlab 2 2 i) ∧ ({t 0, t 1, t 4} : Finset V) = T :=
  (mem_filter.mp ht).2

theorem image_mem_F5 {t : Fin 7 → V} (hinj : Function.Injective t)
    (hlab : ∀ i, lab (t i) = mlab 2 2 i) {p : ℤ × Finset (Fin 7)} (hp : p ∈ I2L) :
    p.2.image t ∈ triG lab F5 := by
  have hok := I2L_ok p hp
  rw [gmem_tri]
  refine ⟨?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj]; exact hok.1
  · intro x _ y _ hxy; exact hxy
  · show (p.2.image t).val.map lab ∈ F5
    have : (p.2.image t).val.map lab = p.2.val.map (mlab 2 2) := by
      rw [show p.2.image t = p.2.map (⟨t, hinj⟩ : Fin 7 ↪ V) by ext x; simp,
        map_val, Multiset.map_map]
      exact Multiset.map_congr rfl fun i _ => hlab i
    rw [this]; exact okTri_F5 hok

theorem sum_list_comm {α β : Type*} (S : Finset α) (l : List β) (g : β → α → ℝ) :
    ∑ x ∈ S, (l.map fun p => g p x).sum = (l.map fun p => ∑ x ∈ S, g p x).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [sum_add_distrib, ih]

/-- The incidence of one placed gadget is twice that of its triangle. -/
theorem gad_incidence {T : Finset V} {t : Fin 7 → V} (ht : t ∈ goods lab T) (e : E0 V) :
    ∑ T' ∈ (triG lab F5).filter (fun T' => e.1 ∈ triEdges T'), gad t T' =
      2 * (if e.1 ∈ triEdges T then 1 else 0) := by
  obtain ⟨hinj, hlab, hT⟩ := goods_spec lab ht
  unfold gad
  rw [sum_list_comm]
  have h1 : ∀ p ∈ I2L, (∑ T' ∈ (triG lab F5).filter (fun T' => e.1 ∈ triEdges T'),
      (p.1 : ℝ) * if T' = p.2.image t then 1 else 0) =
      (p.1 : ℝ) * if e.1 ∈ triEdges (p.2.image t) then 1 else 0 := by
    intro p hp
    rw [← mul_sum, sum_ite_eq']
    simp only [mem_filter, image_mem_F5 lab hinj hlab hp, true_and]
  rw [List.map_congr_left h1]
  have hφ := congrFun (comb_transport (⟨t, hinj⟩ : Fin 7 ↪ V) I2_model) e.1
  rw [combV_apply, combV_apply] at hφ
  have hcast : ∀ l : List (ℤ × Finset (Fin 7)),
      (l.map fun p => (p.1 : ℝ) * if e.1 ∈ triEdges (p.2.image t) then 1 else 0).sum =
        (((l.map fun p => p.1 * if e.1 ∈ triEdges (p.2.map ⟨t, hinj⟩) then 1 else 0).sum : ℤ) :
          ℝ) := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, ih, map_eq_image,
        Function.Embedding.coeFn_mk]
      split_ifs <;> simp
  rw [hcast, hφ, ← hT]
  simp only [I2R, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_insert,
    map_singleton, Function.Embedding.coeFn_mk]
  split_ifs <;> simp

/-- Incidence is preserved. -/
theorem Minc_Psi (hne : ∀ T ∈ aacs lab, (goods lab T).Nonempty) (c : Finset V → ℝ) :
    MincG lab F5 (Psi lab c) = MincG lab cdrF c := by
  funext e
  simp only [MincG, LinearMap.coe_mk, AddHom.coe_mk, Psi]
  rw [sum_add_distrib]
  have hF5 : ∀ T' ∈ (triG lab F5).filter (fun T' => e.1 ∈ triEdges T'),
      (if T' ∈ triG lab F5 then c T' else 0) = c T' := fun T' h => if_pos (mem_filter.mp h).1
  rw [sum_congr rfl hF5, sum_comm]
  have h2 : ∀ T ∈ aacs lab, ∑ T' ∈ (triG lab F5).filter (fun T' => e.1 ∈ triEdges T'),
      c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T' =
      if e.1 ∈ triEdges T then c T else 0 := by
    intro T hT
    rw [← mul_sum, sum_comm, sum_congr rfl fun t ht => gad_incidence lab ht e, sum_const,
      nsmul_eq_mul]
    have hg : ((goods lab T).card : ℝ) ≠ 0 := by
      exact_mod_cast (card_pos.mpr (hne T hT)).ne'
    split_ifs <;> field_simp <;> simp
  rw [sum_congr rfl h2, ← sum_filter]
  -- split the `cdrF` triangles into `F5` and `AAC`
  have hsplit : (triG lab cdrF).filter (fun T => e.1 ∈ triEdges T) =
      (triG lab F5).filter (fun T => e.1 ∈ triEdges T) ∪
        (aacs lab).filter (fun T => e.1 ∈ triEdges T) := by
    ext T
    simp only [mem_filter, mem_union, aacs, gmem_tri]
    constructor
    · rintro ⟨hT, he⟩
      by_cases h : T.val.map lab = aac
      · exact Or.inr ⟨⟨hT, h⟩, he⟩
      · exact Or.inl ⟨⟨hT.1, hT.2.1, hT.2.2, h⟩, he⟩
    · rintro (⟨hT, he⟩ | ⟨⟨hT, -⟩, he⟩)
      · exact ⟨⟨hT.1, hT.2.1, F5_sub hT.2.2⟩, he⟩
      · exact ⟨hT, he⟩
  rw [hsplit, sum_union]
  rw [disjoint_left]
  intro T h1 h2
  simp only [mem_filter, aacs, gmem_tri] at h1 h2
  exact h1.1.2.2.2 h2.1.2

/-! ### Counting placements -/

/-- Placements covering a triangle `T'` with given positions. -/
theorem card_fix3_le {p q r : V} (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (univ.filter fun t : Fin 7 → V => t i = p ∧ t j = q ∧ t k = r).card ≤
      Fintype.card V ^ 4 := by
  set S : Finset (Fin 7) := {i, j, k}
  have hS : S.card = 3 := by
    rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  have hcard : Fintype.card {l // l ∉ S} = 4 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS]
  calc (univ.filter fun t : Fin 7 → V => t i = p ∧ t j = q ∧ t k = r).card
      ≤ Fintype.card ({l // l ∉ S} → V) := by
        refine card_le_card_of_injOn (fun t l => t l.1) (fun _ _ => mem_univ _) ?_
        intro t ht t' ht' h
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
        funext l
        by_cases hl : l ∈ S
        · simp only [S, mem_insert, mem_singleton] at hl
          rcases hl with rfl | rfl | rfl
          · rw [ht.1, ht'.1]
          · rw [ht.2.1, ht'.2.1]
          · rw [ht.2.2, ht'.2.2]
        · exact congrFun h ⟨l, hl⟩
    _ = Fintype.card V ^ 4 := by rw [Fintype.card_fun, hcard]

/-- **At most `343 n⁴` placements cover a given triangle.** -/
theorem card_cover_le {T' : Finset V} (h3 : T'.card = 3) :
    (univ.filter fun t : Fin 7 → V => T' ⊆ univ.image t).card ≤ 343 * Fintype.card V ^ 4 := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp h3
  have hsub : (univ.filter fun t : Fin 7 → V => ({p, q, r} : Finset V) ⊆ univ.image t) ⊆
      (univ : Finset (Fin 7 × Fin 7 × Fin 7)).biUnion fun ijk =>
        univ.filter fun t : Fin 7 → V => t ijk.1 = p ∧ t ijk.2.1 = q ∧ t ijk.2.2 = r := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and, insert_subset_iff, singleton_subset_iff,
      mem_image] at ht
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ := ht
    exact mem_biUnion.mpr ⟨(i, j, k), mem_univ _, by simp [hi, hj, hk]⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  calc ∑ ijk : Fin 7 × Fin 7 × Fin 7,
        (univ.filter fun t : Fin 7 → V => t ijk.1 = p ∧ t ijk.2.1 = q ∧ t ijk.2.2 = r).card
      ≤ ∑ _ijk : Fin 7 × Fin 7 × Fin 7, Fintype.card V ^ 4 := by
        refine sum_le_sum fun ijk _ => ?_
        obtain ⟨i, j, k⟩ := ijk
        by_cases hij : i = j
        · subst hij
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨h1, h2, -⟩; exact hpq (h1 ▸ h2)
        by_cases hik : i = k
        · subst hik
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨h1, -, h3⟩; exact hpr (h1 ▸ h3)
        by_cases hjk : j = k
        · subst hjk
          rw [card_eq_zero.mpr]; · exact Nat.zero_le _
          ext t; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          rintro ⟨-, h2, h3⟩; exact hqr (h2 ▸ h3)
        exact card_fix3_le i j k hij hik hjk
    _ = 343 * Fintype.card V ^ 4 := by simp

theorem list_abs_le (l : List (ℤ × Finset (Fin 7))) (f : Finset (Fin 7) → ℝ)
    (hf : ∀ S, |f S| ≤ 1) :
    |(l.map fun p => (p.1 : ℝ) * f p.2).sum| ≤ (l.map fun p => |(p.1 : ℝ)|).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf _)

theorem list_zero (l : List (ℤ × Finset (Fin 7))) (f : Finset (Fin 7) → ℝ)
    (hf : ∀ p ∈ l, f p.2 = 0) : (l.map fun p => (p.1 : ℝ) * f p.2).sum = 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, hf p List.mem_cons_self, mul_zero, zero_add]
    exact ih fun q hq => hf q (List.mem_cons_of_mem _ hq)

theorem abs_gad_le (t : Fin 7 → V) (T' : Finset V) : |gad t T'| ≤ 18 := by
  unfold gad
  refine (list_abs_le I2L (fun S => if T' = S.image t then 1 else 0)
    (fun S => by split_ifs <;> simp)).trans (le_of_eq ?_)
  simp [I2L]; norm_num

theorem gad_zero_cover {t : Fin 7 → V} {T' : Finset V} (h : ¬ T' ⊆ univ.image t) :
    gad t T' = 0 := by
  unfold gad
  refine list_zero I2L (fun S => if T' = S.image t then 1 else 0) fun p _ => ?_
  rw [if_neg]
  rintro rfl
  exact h (image_subset_image (subset_univ _))

theorem gad_zero_card {t : Fin 7 → V} (hinj : Function.Injective t) {T' : Finset V}
    (h : T'.card ≠ 3) : gad t T' = 0 := by
  unfold gad
  refine list_zero I2L (fun S => if T' = S.image t then 1 else 0) fun p hp => ?_
  rw [if_neg]
  rintro rfl
  exact h (by rw [card_image_of_injective _ hinj]; exact (I2L_ok p hp).1)

/-- Placements of distinct triangles are distinct. -/
theorem goods_disjoint {T₁ T₂ : Finset V} (h : T₁ ≠ T₂) : Disjoint (goods lab T₁) (goods lab T₂) := by
  rw [disjoint_left]
  intro t h1 h2
  exact h ((goods_spec lab h1).2.2.symm.trans (goods_spec lab h2).2.2)

/-- **The bound**: if every `AAC` triangle has at least `M > 0` placements and `|c| ≤ β`,
then `|Ψ c| ≤ (1 + 9·343 n⁴/M)·β`. -/
theorem abs_Psi_le {M : ℝ} (hM : 0 < M) (hg : ∀ T ∈ aacs lab, M ≤ (goods lab T).card)
    {c : Finset V → ℝ} {β : ℝ} (hβ : ∀ T, |c T| ≤ β) (T' : Finset V) :
    |Psi lab c T'| ≤ (1 + 9 * 343 * (Fintype.card V : ℝ) ^ 4 / M) * β := by
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ T')
  simp only [Psi, LinearMap.coe_mk, AddHom.coe_mk]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(if T' ∈ triG lab F5 then c T' else 0)| ≤ β := by
    split_ifs
    · exact hβ T'
    · simpa using hβ0
  have h2 : |∑ T ∈ aacs lab, c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T'| ≤
      9 * 343 * (Fintype.card V : ℝ) ^ 4 / M * β := by
    by_cases h3 : T'.card = 3
    · set cov : Finset (Fin 7 → V) := univ.filter fun t : Fin 7 → V => T' ⊆ univ.image t
      have hterm : ∀ T ∈ aacs lab,
          |c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T'| ≤
            9 * β / M * ((goods lab T).filter (· ∈ cov)).card := by
        intro T hT
        have hgT := hg T hT
        have hgpos : (0 : ℝ) < (goods lab T).card := hM.trans_le hgT
        have hs : |∑ t ∈ goods lab T, gad t T'| ≤
            18 * ((goods lab T).filter (· ∈ cov)).card := by
          rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
          by_cases ht : t ∈ cov
          · rw [if_pos ht]; simpa using abs_gad_le t T'
          · rw [if_neg ht]
            simp only [cov, mem_filter, mem_univ, true_and] at ht
            simp [gad_zero_cover ht]
        have hc : |c T / (2 * (goods lab T).card)| ≤ β / (2 * M) := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (goods lab T).card)]
          exact div_le_div₀ hβ0 (hβ T) (by positivity) (by linarith)
        rw [abs_mul]
        calc |c T / (2 * (goods lab T).card)| * |∑ t ∈ goods lab T, gad t T'|
            ≤ β / (2 * M) * (18 * ((goods lab T).filter (· ∈ cov)).card) :=
              mul_le_mul hc hs (abs_nonneg _) (by positivity)
          _ = 9 * β / M * ((goods lab T).filter (· ∈ cov)).card := by field_simp; ring
      have hdisj : ((aacs lab : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
          fun T => (goods lab T).filter (· ∈ cov) := by
        intro T₁ _ T₂ _ h
        exact disjoint_filter_filter (goods_disjoint lab h)
      have hcov : ∑ T ∈ aacs lab, (((goods lab T).filter (· ∈ cov)).card : ℝ) ≤ cov.card := by
        rw [← Nat.cast_sum, ← card_biUnion hdisj]
        exact_mod_cast card_le_card fun t ht => by
          obtain ⟨T, -, ht⟩ := mem_biUnion.mp ht
          exact (mem_filter.mp ht).2
      have hcov2 : (cov.card : ℝ) ≤ 343 * (Fintype.card V : ℝ) ^ 4 := by
        exact_mod_cast card_cover_le h3
      calc |∑ T ∈ aacs lab, c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T'|
          ≤ ∑ T ∈ aacs lab, 9 * β / M * ((goods lab T).filter (· ∈ cov)).card :=
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
        _ = 9 * β / M * ∑ T ∈ aacs lab, (((goods lab T).filter (· ∈ cov)).card : ℝ) := by
            rw [mul_sum]
        _ ≤ 9 * β / M * (343 * (Fintype.card V : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left (hcov.trans hcov2) (by positivity)
        _ = 9 * 343 * (Fintype.card V : ℝ) ^ 4 / M * β := by ring
    · have : ∀ T ∈ aacs lab, c T / (2 * (goods lab T).card) * ∑ t ∈ goods lab T, gad t T' = 0 := by
        intro T _
        rw [sum_eq_zero fun t ht => gad_zero_card (goods_spec lab ht).1 h3, mul_zero]
      rw [sum_eq_zero this, abs_zero]
      positivity
  calc _ ≤ β + 9 * 343 * (Fintype.card V : ℝ) ^ 4 / M * β := add_le_add h1 h2
    _ = _ := by ring

/-! ### Many placements, and the bounded inverse -/

theorem aac_shape_c {T : Finset V} (hT : T ∈ aacs lab) :
    ∃ u v w, T = {u, v, w} ∧ lab u = 0 ∧ lab v = 0 ∧ lab w = 2 ∧ u ≠ v := by
  simp only [aacs, mem_filter, gmem_tri] at hT
  obtain ⟨⟨h3, -, -⟩, haac⟩ := hT
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp h3
  rw [show ({p, q, r} : Finset V).val.map lab = ({lab p, lab q, lab r} : Multiset (Fin 3)) from
    val_map_triple lab hpq hpr.symm hqr.symm] at haac
  have key : ∀ x y z : Fin 3, ({x, y, z} : Multiset (Fin 3)) = aac →
      (x = 0 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 2 ∧ z = 0) ∨ (x = 2 ∧ y = 0 ∧ z = 0) := by
    unfold aac; decide
  rcases key _ _ _ haac with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨p, q, r, rfl, h1, h2, h3, hpq⟩
  · exact ⟨p, r, q, by ext; simp; tauto, h1, h3, h2, hpr⟩
  · exact ⟨q, r, p, by ext; simp; tauto, h2, h3, h1, hqr⟩

/-- **Many placements**: `|B|(|B|−1)(|C|−1)(|C|−2)` at least. -/
theorem goods_card_ge {T : Finset V} (hT : T ∈ aacs lab) :
    csz lab 1 * (csz lab 1 - 1) * ((csz lab 2 - 1) * (csz lab 2 - 1 - 1)) ≤ (goods lab T).card := by
  obtain ⟨u, v, w, rfl, hu, hv, hw, huv⟩ := aac_shape_c lab hT
  set Bs := univ.filter fun x => lab x = 1
  set Cs := (univ.filter fun x => lab x = 2).erase w
  have hCs : Cs.card = csz lab 2 - 1 := by
    rw [card_erase_of_mem (by simp [hw])]; rfl
  have hD : (Bs.offDiag ×ˢ Cs.offDiag).card =
      csz lab 1 * (csz lab 1 - 1) * ((csz lab 2 - 1) * (csz lab 2 - 1 - 1)) := by
    rw [card_product, offDiag_card, offDiag_card, hCs]
    have : Bs.card = csz lab 1 := rfl
    rw [this, ← Nat.mul_sub_one, ← Nat.mul_sub_one]
  rw [← hD]
  refine card_le_card_of_injOn (fun x => ![u, v, x.1.1, x.1.2, w, x.2.1, x.2.2]) ?_ ?_
  · intro x hx
    simp only [coe_product, Set.mem_prod, mem_coe, mem_offDiag, Bs, Cs, mem_filter, mem_univ,
      true_and, mem_erase] at hx
    obtain ⟨⟨hb2, hb3, hb23⟩, ⟨⟨hc5w, hc5⟩, ⟨hc6w, hc6⟩, hc56⟩⟩ := hx
    try simp only [Finset.mem_coe]
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩
    · apply inj_of_list
      simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      have l1 := ne_of_lab (lab := lab) (x := u) (y := x.1.1) (by rw [hu, hb2]; decide)
      have l2 := ne_of_lab (lab := lab) (x := u) (y := x.1.2) (by rw [hu, hb3]; decide)
      have l3 := ne_of_lab (lab := lab) (x := u) (y := w) (by rw [hu, hw]; decide)
      have l4 := ne_of_lab (lab := lab) (x := u) (y := x.2.1) (by rw [hu, hc5]; decide)
      have l5 := ne_of_lab (lab := lab) (x := u) (y := x.2.2) (by rw [hu, hc6]; decide)
      have l6 := ne_of_lab (lab := lab) (x := v) (y := x.1.1) (by rw [hv, hb2]; decide)
      have l7 := ne_of_lab (lab := lab) (x := v) (y := x.1.2) (by rw [hv, hb3]; decide)
      have l8 := ne_of_lab (lab := lab) (x := v) (y := w) (by rw [hv, hw]; decide)
      have l9 := ne_of_lab (lab := lab) (x := v) (y := x.2.1) (by rw [hv, hc5]; decide)
      have l10 := ne_of_lab (lab := lab) (x := v) (y := x.2.2) (by rw [hv, hc6]; decide)
      have l11 := ne_of_lab (lab := lab) (x := x.1.1) (y := w) (by rw [hb2, hw]; decide)
      have l12 := ne_of_lab (lab := lab) (x := x.1.1) (y := x.2.1) (by rw [hb2, hc5]; decide)
      have l13 := ne_of_lab (lab := lab) (x := x.1.1) (y := x.2.2) (by rw [hb2, hc6]; decide)
      have l14 := ne_of_lab (lab := lab) (x := x.1.2) (y := w) (by rw [hb3, hw]; decide)
      have l15 := ne_of_lab (lab := lab) (x := x.1.2) (y := x.2.1) (by rw [hb3, hc5]; decide)
      have l16 := ne_of_lab (lab := lab) (x := x.1.2) (y := x.2.2) (by rw [hb3, hc6]; decide)
      refine ⟨⟨huv, ?_⟩, ?_⟩ <;> simp_all [Ne.symm, eq_comm]
    · intro i; fin_cases i <;> simp [mlab, hu, hv, hb2, hb3, hw, hc5, hc6]
    · simp
  · intro x hx y hy hxy
    have e2 := congrFun hxy 2
    have e3 := congrFun hxy 3
    have e5 := congrFun hxy 5
    have e6 := congrFun hxy 6
    simp at e2 e3 e5 e6
    exact Prod.ext (Prod.ext e2 e3) (Prod.ext e5 e6)

/-- **Bounded inverse of the five-type host.** -/
def bri5 {w : Sym2 V → ℝ} {K : ℝ} (hK : 0 ≤ K) (B : BRIG lab cdrF w K) {M : ℝ} (hM : 0 < M)
    (hg : ∀ T ∈ aacs lab, M ≤ (goods lab T).card) :
    BRIG lab F5 w ((1 + 9 * 343 * (Fintype.card V : ℝ) ^ 4 / M) * K) where
  Φ := Psi lab ∘ₗ B.Φ
  exact d hd := by
    rw [LinearMap.comp_apply, Minc_Psi lab (fun T hT => card_pos.mp (by
      have := hM.trans_le (hg T hT); exact_mod_cast this)), B.exact d hd]
  bound d hd T := by
    have := abs_Psi_le lab hM hg (β := K / Fintype.card V * ‖d‖) (fun T' => B.bound d hd T') T
    rw [LinearMap.comp_apply]
    refine this.trans (le_of_eq ?_)
    ring

end CDRBicolour.Absorption.Extremes
