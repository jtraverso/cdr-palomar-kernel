/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ClonedPacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone

/-- EGJ applied to a genuine simple hypergraph of tagged copies. The degree
and codegree obligations are explicit sums of original multiplicities, not an
assumed matching or a regularization provider. -/
theorem matching_from_integer_multiplicities (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (r : ℕ) (hr : 1≤r) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀≤D → 1≤D →
    ∀ (E ι : Type) [Fintype E] [Fintype ι] (P : ι → Finset E) (m : ι → ℕ),
      (∀ i, (P i).card=r) →
      (∀ e, ((∑ i, if e∈P i then m i else 0 : ℕ):ℝ)≤D) →
      (∀ e f, e≠f → ((∑ i, if e∈P i ∧ f∈P i then m i else 0 : ℕ):ℝ)≤D^(1-δ)) →
      ((∑ i, m i : ℕ):ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∀ (κ : Type) [Fintype κ] (W : κ → ι → ℝ),
      (∀ k i, 0≤W k i) →
      (Fintype.card κ:ℝ)≤Real.exp (D^((δ/(50*(r+1)^2))^2)) →
      ∃ C : Finset (Copy m),
        (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) ∧
        ∀ k, (∀ i, 0 < m i → W k i*D^(1+δ)≤∑ j, (m j:ℝ)*W k j) →
          |(∑ c ∈ C, W k c.1)-(∑ i, (m i:ℝ)*W k i)/D|≤
            D^(-(δ/(50*(r+1)^2)))*((∑ i, (m i:ℝ)*W k i)/D) := by
  obtain ⟨D₀,hEGJ⟩ := Pseudorandom.theorem_1_2 δ hδ hδ1 (r+1) (by omega)
  refine ⟨D₀,?_⟩
  intro D hD₀ hD E ι _ _ P m hcard hdeg hcode hsize κ _ W hW hκ
  have hpow : 1≤D^(1-δ) := Real.one_le_rpow hD (by linarith)
  have hdegree : ∀ v : E ⊕ Copy m,
      (Pseudorandom.degree (hypergraph P m) v:ℝ)≤D := by
    intro v
    cases v with
    | inl e => simpa only [degree_left] using hdeg e
    | inr c => simpa only [degree_right,Nat.cast_one] using hD
  have hcodegree : ∀ u v : E ⊕ Copy m, u≠v →
      (Pseudorandom.codegree (hypergraph P m) u v:ℝ)≤D^(1-δ) := by
    intro u v huv
    cases u with
    | inl e =>
      cases v with
      | inl f => exact (by simpa only [codegree_left] using hcode e f (by simpa using huv))
      | inr c => exact (show (Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c):ℝ)≤1 by exact_mod_cast codegree_mixed_le P m e c).trans hpow
    | inr c =>
      cases v with
      | inl e =>
        have heq : Pseudorandom.codegree (hypergraph P m) (Sum.inr c) (Sum.inl e)=
            Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c) := by
          simp only [Pseudorandom.codegree,and_comm]
        rw [heq]
        exact (show (Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c):ℝ)≤1 by exact_mod_cast codegree_mixed_le P m e c).trans hpow
      | inr d =>
        rw [codegree_right_eq_zero P m (by simpa using huv),Nat.cast_zero]
        exact le_trans zero_le_one hpow
  obtain ⟨M,hMH,hM,hweights⟩ := hEGJ D hD₀ (E ⊕ Copy m) (hypergraph P m)
    (hypergraph_uniform P m hcard) hdegree hcodegree (by simpa only [hypergraph_card,Nat.cast_add,Nat.cast_one] using hsize)
    κ (fun k => liftedWeight P m (W k)) (by
      intro k T hT
      obtain ⟨c,_,rfl⟩ := mem_image.mp hT
      rw [liftedWeight_packet]
      exact hW k c.1) (by simpa only [Nat.cast_add,Nat.cast_one] using hκ)
  obtain ⟨C,hMC,hDis,hWC⟩ := extract_matching P m hMH hM
  refine ⟨C,hDis,?_⟩
  intro k hmass
  have hbound := hweights k (by
    intro T hT
    obtain ⟨c,_,rfl⟩ := mem_image.mp hT
    rw [liftedWeight_packet,weight_hypergraph]
    exact hmass c.1 (Nat.zero_lt_of_lt c.2.2))
  rw [hWC (W k),weight_hypergraph] at hbound
  simpa only [Nat.cast_add,Nat.cast_one] using hbound

end TypedTriangle.WeightedClone
