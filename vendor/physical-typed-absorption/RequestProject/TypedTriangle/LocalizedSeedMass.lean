/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.WeightedStars
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedStar
variable {V I : Type*} [Fintype V]

def localEnvelope (Z T : Finset V) : ℝ := (T∩Z).card/3

omit [Fintype V] in
lemma sum_starWeight_bad (Z T : Finset V) :
    (∑ v ∈ Z, starWeight v T) = ((T∩Z).card:ℝ) := by
  simp [starWeight,sum_ite_mem,inter_comm]

lemma localEnvelope_bounds (Z : Finset V) {H : Host V I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed H F T) :
    0 ≤ localEnvelope Z T ∧ localEnvelope Z T ≤ 1 := by
  have hc : (T∩Z).card ≤ 3 := (card_le_card inter_subset_left).trans hT.1.le
  have hc' : ((T∩Z).card:ℝ) ≤ 3 := by exact_mod_cast hc
  unfold localEnvelope
  constructor
  · positivity
  · linarith

/-- The localized envelope has exactly one third of the total fractional
star mass at Z. This identity uses the actual diffuse seed, not a quota. -/
lemma localEnvelope_mass_identity (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (Z : Finset V) :
    3*(∑ T ∈ allowed H F, φ T*localEnvelope Z T) =
      ∑ v ∈ Z, ∑ T ∈ allowed H F, φ T*starWeight v T := by
  rw [sum_comm]
  rw [mul_sum]
  apply sum_congr rfl
  intro T _
  rw [←mul_sum,sum_starWeight_bad]
  unfold localEnvelope
  ring

/-- Uniform linear lower mass whenever Z meets an active root, and the sharp
O(n |Z|) upper mass. No lower bound on |Z|/n is required. -/
theorem localEnvelope_mass_bounds (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) {C α : ℝ} (hC : 0 < C)
    (hφ : IsDiffuseSeed H F C φ) (h3 : CommonNbrCond H F α) (Z : Finset V)
    (hZ : ∃ v ∈ Z, ActiveRoot H F v) :
    α/6*Fintype.card V ≤ (∑ T ∈ allowed H F, φ T*localEnvelope Z T) ∧
      (∑ T ∈ allowed H F, φ T*localEnvelope Z T) ≤
        Fintype.card V*Z.card/6 := by
  have hφ0 : ∀ T ∈ allowed H F, 0 ≤ φ T := by
    intro T hT
    exact (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
      (hφ.1 T (isAllowed_of_mem_allowed hT)).1
  have hstar0 : ∀ v, 0 ≤ ∑ T ∈ allowed H F, φ T*starWeight v T := by
    intro v
    apply sum_nonneg
    intro T hT
    apply mul_nonneg (hφ0 T hT)
    dsimp [starWeight]
    split_ifs <;> norm_num
  have hid := localEnvelope_mass_identity H F φ Z
  obtain ⟨v,hv,hAct⟩ := hZ
  have hlo := (seed_star_mass_bounds H F φ hφ h3 hAct).1
  have hsingle := single_le_sum (f:=fun v => ∑ T ∈ allowed H F, φ T*starWeight v T)
    (fun v _ => hstar0 v) hv
  have hupper : (∑ v ∈ Z, ∑ T ∈ allowed H F, φ T*starWeight v T) ≤
      Fintype.card V*Z.card/2 := by
    calc _ ≤ ∑ _v ∈ Z, (Fintype.card V:ℝ)/2 := by
          apply sum_le_sum
          intro v _
          have hs := seed_star_identity H F φ hφ v
          have hn : ((nbrsIn (edges H) v).card:ℝ) ≤ Fintype.card V := by
            exact_mod_cast card_le_univ _
          linarith
         _ = _ := by simp; ring
  constructor <;> nlinarith only [hid,hlo,hsingle,hupper]

end TypedTriangle.WeightedStar
