/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ExplicitApproxPackingGeometry
public import RequestProject.TypedTriangle.ExplicitCeilPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PartitionedTriangleAbsorption.Nibble.Explicit
open TypedTriangle.WeightedClone

def approxPackingCut (b η : ℝ) : ℕ :=
  max 1 ⌈TypedTriangle.WeightedClone.Explicit.cloneCut (max 1 b) (η/16) (η/8)
    (Pseudorandom.Explicit.egjCut (1/4) 4) 1⌉₊

/-- Near-unit loads, including zero individual triangle weights, admit a real
packing at the displayed finite EGJ threshold. -/
theorem nibble_packing_near_explicit (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ (V : Type) [Fintype V] [DecidableEq V], approxPackingCut b η ≤ Fintype.card V →
    ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
      (∀ i, triEdges (S.tri i) ⊆ B) →
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ b/Fintype.card V) →
      (∀ e ∈ B, |S.load w e-1| ≤ η/8) →
      ∃ P : Finset (Fin m), IsPacking S P ∧
        ∀ v, ((star (B\edgesOf S P) v).card : ℝ) ≤ η*Fintype.card V := by
  intro V _ _ hn m S B w hB hw hwb hload
  let n : ℝ := Fintype.card V
  let ε := η/8
  let ψ : Fin m → ℝ := fun i => w i/(1+ε)
  let A : Finset V := univ.filter fun v => η*n/2 ≤ (star B v).card
  let W : ↥A → Fin m → ℝ := fun v i => if (v : V) ∈ S.tri i then 1 else 0
  have hn1 : 1 ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast (by omega : 0 < Fintype.card V)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1/8 := by dsimp [ε]; linarith
  have hden : 0 < 1+ε := by linarith
  have hψ0 : ∀ i, 0 ≤ ψ i := fun i => div_nonneg (hw i) hden.le
  have hψ : ∀ i, 0 ≤ ψ i ∧ ψ i ≤ max 1 b/n := by
    intro i
    refine ⟨hψ0 i, ?_⟩
    calc ψ i ≤ w i := div_le_self (hw i) (by linarith)
      _ ≤ b/n := hwb i
      _ ≤ max 1 b/n := div_le_div_of_nonneg_right (le_max_right _ _) hnpos.le
  have hψload (e : Sym2 V) : S.load ψ e = S.load w e/(1+ε) := by
    simp only [TriSystem.load, ψ, sum_div]
  have hloads : ∀ e, ∑ i, (if e ∈ triEdges (S.tri i) then ψ i else 0) ≤ 1 := by
    intro e
    change (∑ i, if e ∈ triEdges (S.tri i) then ψ i else 0) ≤ 1
    have heq : (∑ i, if e ∈ triEdges (S.tri i) then ψ i else 0) = S.load ψ e := by
      simp only [TriSystem.load, TriSystem.edgeTris, sum_filter]
    rw [heq, hψload]
    by_cases he : e ∈ B
    · exact (div_le_one hden).mpr (by have hh := (abs_le.mp (hload e he)).2; dsimp [ε]; linarith)
    · have he0 : S.load w e = 0 := by
        apply sum_eq_zero
        intro i hi
        exact False.elim (he (hB i ((S.mem_edgeTris).mp hi)))
      rw [he0, zero_div]
      norm_num
  have hmass (v : ↥A) : (η/16)*n ≤ ∑ i, ψ i*W v i := by
    have hv : η*n/2 ≤ (star B (v : V)).card := (mem_filter.mp v.property).2
    have hlo : (1-2*ε)*(star B (v : V)).card ≤ ∑ e ∈ star B (v : V), S.load ψ e := by
      calc (1-2*ε)*(star B (v : V)).card = ∑ _ ∈ star B (v : V), (1-2*ε) := by simp; ring
        _ ≤ ∑ e ∈ star B (v : V), S.load ψ e := by
          apply sum_le_sum
          intro e he
          rw [hψload]
          apply (le_div_iff₀ hden).mpr
          have hh := (abs_le.mp (hload e (mem_filter.mp he).1)).1
          dsimp [ε] at *
          nlinarith [sq_nonneg η]
    have hstar := S.sum_star_load B hB ψ (v : V)
    have heq : (∑ i, ψ i*W v i) = ∑ i ∈ S.through (v : V), ψ i := by
      simp only [W, TriSystem.through, sum_filter, mul_ite, mul_one, mul_zero]
    rw [hstar, ← heq] at hlo
    have hdeg : (0 : ℝ) ≤ (star B (v : V)).card := by positivity
    have hcoeff := mul_le_mul_of_nonneg_right (show (3:ℝ)/4 ≤ 1-2*ε by linarith) hdeg
    nlinarith
  have hE : (Fintype.card (Sym2 V) : ℝ) ≤ n^2 := by
    have hh := Fintype.card_le_of_surjective (Sym2.mk (α:=V)).uncurry Sym2.mk_surjective
    have hh' : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by simpa [pow_two] using hh
    dsimp only [n]
    exact_mod_cast hh'
  have hcut : TypedTriangle.WeightedClone.Explicit.cloneCut (max 1 b) (η/16) (η/8)
      (Pseudorandom.Explicit.egjCut (1/4) 4) 1 ≤ n :=
    (Nat.le_ceil _).trans (by dsimp only [n]; exact_mod_cast (le_max_right _ _).trans hn)
  obtain ⟨P,hP,hW⟩ := TypedTriangle.WeightedClone.Explicit.ceil_matching_lower_explicit
    (max 1 b) (η/16) (η/8) 1 (le_max_left _ _) (by positivity) (by positivity)
    (by linarith) n hcut (Sym2 V) (Fin m) ↥A (fun i => triEdges (S.tri i)) ψ W hE
    (by simpa only [Fintype.card_fin] using S.total_triangles_le_vertices_cube)
    (fun i => card_triEdges (S.card_tri i)) hψ
    (fun e => by
      convert hloads e using 1
      apply sum_congr rfl
      intro i _
      split_ifs <;> rfl)
    (fun e => by
      have hh : ((S.edgeTris e).card : ℝ) ≤ n := by
        dsimp only [n]
        exact_mod_cast S.edgeTris_card_le_vertices e
      convert hh using 1
      congr 2
      ext i
      simp only [TriSystem.edgeTris, mem_filter, mem_univ, true_and])
    (fun e f hef => by
      convert S.edgeTris_inter_card_le hef using 1
      congr 1
      ext i
      simp only [TriSystem.edgeTris, mem_filter, mem_univ, true_and])
    (by simpa only [pow_one, Fintype.card_coe] using (show (A.card : ℝ) ≤ n by dsimp only [n]; exact_mod_cast card_le_univ A))
    (by intro v i; dsimp [W]; split_ifs <;> norm_num) hmass
  have hpack : IsPacking S P := fun i hi j hj hij => hP hi hj hij
  refine ⟨P,hpack,?_⟩
  intro v
  have hsub : edgesOf S P ⊆ B := by
    intro e he
    obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
    exact hB i he
  have hstarSub := star_mono hsub v
  have hcard : (star (B\edgesOf S P) v).card+(star (edgesOf S P) v).card = (star B v).card := by
    have he : star (B\edgesOf S P) v = star B v\star (edgesOf S P) v := by ext e; simp [star]; tauto
    rw [he]
    exact card_sdiff_add_card_eq_card hstarSub
  have hdeg : ((star B v).card : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast card_star_le B v
  have hrem : ((star (B\edgesOf S P) v).card : ℝ) ≤ (star B v).card := by exact_mod_cast (by omega : (star (B\edgesOf S P) v).card ≤ (star B v).card)
  by_cases hv : v ∈ A
  · have hselected := hW ⟨v,hv⟩
    have heq : (∑ i ∈ P, W ⟨v,hv⟩ i) = ((P.filter fun i => v ∈ S.tri i).card : ℝ) := by simp [W, sum_filter]
    rw [heq] at hselected
    have hlo : (1-2*ε)*(star B v).card ≤ 2*(∑ i, ψ i*W ⟨v,hv⟩ i) := by
      have heq : (∑ i, ψ i*W ⟨v,hv⟩ i) = ∑ i ∈ S.through v, ψ i := by
        simp only [W, TriSystem.through, sum_filter, mul_ite, mul_one, mul_zero]
      rw [heq, ← S.sum_star_load B hB ψ v]
      calc (1-2*ε)*(star B v).card = ∑ _ ∈ star B v, (1-2*ε) := by simp; ring
        _ ≤ _ := by
          apply sum_le_sum
          intro e he
          rw [hψload]
          apply (le_div_iff₀ hden).mpr
          have hh := (abs_le.mp (hload e (mem_filter.mp he).1)).1
          dsimp [ε] at *
          nlinarith [sq_nonneg η]
    have hfactor : (1-η) ≤ (1-η/8)*(1-2*ε) := by dsimp [ε]; nlinarith [sq_nonneg η]
    have hfac0 : 0 ≤ 1-η/8 := by linarith
    have hm := mul_le_mul_of_nonneg_left hlo hfac0
    have hf := mul_le_mul_of_nonneg_right hfactor (show (0 : ℝ) ≤ (star B v).card by positivity)
    have hcR : ((star (B\edgesOf S P) v).card : ℝ)+2*(P.filter fun i => v ∈ S.tri i).card = (star B v).card := by
      rw [S.card_star_edgesOf P hpack] at hcard
      exact_mod_cast hcard
    have hηdeg := mul_le_mul_of_nonneg_left hdeg hη.le
    nlinarith
  · have hv' : ((star B v).card : ℝ) < η*n/2 := by simpa [A] using hv
    linarith

#print axioms nibble_packing_near_explicit
end PartitionedTriangleAbsorption.Nibble.Explicit
