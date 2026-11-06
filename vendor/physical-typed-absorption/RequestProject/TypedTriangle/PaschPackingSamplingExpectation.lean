module
public import RequestProject.TypedTriangle.PaschStatistics
public import RequestProject.TypedTriangle.BasalPackingIncidence
public import RequestProject.TypedTriangle.VortexBernoulliRestriction
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TypedTriangle.Pasch
variable {V : Type*}

theorem configurations_subfamily (P D : Finset (Finset V)) (hD : D ⊆ P) :
    configurations D = (configurations P).filter (fun K => K ⊆ D) := by
  ext K
  simp only [mem_filter,mem_configurations]
  constructor
  · rintro ⟨hKD,hKc,hK⟩
    exact ⟨⟨hKD.trans hD,hKc,hK⟩,hKD⟩
  · rintro ⟨⟨_,hKc,hK⟩,hKD⟩
    exact ⟨hKD,hKc,hK⟩

theorem count_eq_sum_subset_indicator (P D : Finset (Finset V)) (hD : D ⊆ P) :
    (count D : ℝ) = ∑ K ∈ configurations P, if K ⊆ D then (1 : ℝ) else 0 := by
  rw [sum_boole,←configurations_subfamily P D hD]
  rfl

/-- Four distinct blocks survive independent block sampling with probability q^4. -/
theorem bexp_count_subpacking (q : ℝ) (P : Finset (Finset V)) :
    bexp q P (fun D => (count D : ℝ)) = q^4*(count P : ℝ) := by
  calc
    _ = bexp q P (fun D => ∑ K ∈ configurations P,
        if K ⊆ D then (1 : ℝ) else 0) :=
      bexp_congr (fun D hD => count_eq_sum_subset_indicator P D hD)
    _ = ∑ K ∈ configurations P,
        bexp q P (fun D => if K ⊆ D then (1 : ℝ) else 0) := bexp_sum _ _ _
    _ = ∑ _K ∈ configurations P, q^4 := by
      apply sum_congr rfl
      intro K hK
      rw [bexp_subset_ind P K (mem_configurations.mp hK).1,
        (mem_configurations.mp hK).2.1]
    _ = _ := by simp [count,mul_comm]

theorem bexp_count_selected (q : ℝ) (P : Finset (Finset V)) :
    bexp q (univ : Finset P) (fun W => (count (BasalIncidence.selected W) : ℝ)) =
      q^4*(count P : ℝ) := by
  let e : P ↪ Finset V := Function.Embedding.subtype (fun T => T ∈ P)
  have hMap : (univ : Finset P).map e = P := by
    ext T
    constructor
    · intro hT
      obtain ⟨b,_,rfl⟩ := mem_map.mp hT
      exact b.property
    · intro hT
      exact mem_map.mpr ⟨⟨T,hT⟩,mem_univ _,rfl⟩
  have hSel : ∀ W : Finset P, W.map e = BasalIncidence.selected W := by
    intro W
    rw [map_eq_image]
    rfl
  calc
    _ = bexp q P (fun D => (count D : ℝ)) := by
      simpa only [hMap,hSel] using
        (bexp_map q (univ : Finset P) e (fun D => (count D : ℝ))).symm
    _ = _ := bexp_count_subpacking q P

end TypedTriangle.Pasch

namespace S07V24
variable {A : Type*} [DecidableEq A]

theorem bprob_upper_le_bexp_div (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (U : Finset A) (f : Finset A → ℝ) (hf : ∀ W ⊆ U, 0 ≤ f W)
    (t : ℝ) (ht : 0 < t) :
    bprob q U (fun W => t ≤ f W) ≤ bexp q U f/t := by
  have hPoint : ∀ W ⊆ U,
      t*(if t ≤ f W then (1 : ℝ) else 0) ≤ f W := by
    intro W hW
    by_cases h : t ≤ f W
    · simpa only [if_pos h,mul_one] using h
    · simpa only [if_neg h,mul_zero] using hf W hW
  have hExp := bexp_mono hq hq1 hPoint
  rw [bexp_smul] at hExp
  change t*bprob q U (fun W => t ≤ f W) ≤ bexp q U f at hExp
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hExp)

end S07V24

#print axioms TypedTriangle.Pasch.bexp_count_subpacking
#print axioms TypedTriangle.Pasch.bexp_count_selected
#print axioms S07V24.bprob_upper_le_bexp_div
