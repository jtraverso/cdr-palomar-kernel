module
public import RequestProject.TypedTriangle.WeightedStars
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]
open WeightedStar

theorem activeRoot_of_positive_seed_degree {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hSeed : IsDiffuseSeed H F C μ) (v : V)
    (hdeg : 0 < (nbrsIn (edges H) v).card) : ActiveRoot H F v := by
  by_contra hn
  have hz : (∑ T ∈ allowed H F, μ T * starWeight v T) = 0 := by
    apply sum_eq_zero
    intro T hT
    have hv : v ∉ T := fun hv => hn ⟨T, isAllowed_of_mem_allowed hT, hv⟩
    simp only [starWeight, if_neg hv, mul_zero]
  have hid := seed_star_identity H F μ hSeed v
  rw [hz, mul_zero] at hid
  have hd : (nbrsIn (edges H) v).card = 0 := by exact_mod_cast hid.symm
  omega

theorem positive_seed_degree_lower {H : Host V I} {F : Set (Multiset I)}
    {C α : ℝ} {μ : Finset V → ℝ} (hSeed : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (v : V) (hdeg : 0 < (nbrsIn (edges H) v).card) :
    α * Fintype.card V ≤ (nbrsIn (edges H) v).card :=
  active_degree_lower hH3 (activeRoot_of_positive_seed_degree hSeed v hdeg)

theorem star_seed_mass_zero_or_lower {H : Host V I} {F : Set (Multiset I)}
    {C α : ℝ} {μ : Finset V → ℝ} (hSeed : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (v : V) :
    (∑ T ∈ allowed H F, μ T * starWeight v T) = 0 ∨
      α / 2 * Fintype.card V ≤ ∑ T ∈ allowed H F, μ T * starWeight v T := by
  by_cases hdeg : 0 < (nbrsIn (edges H) v).card
  · exact Or.inr (seed_star_mass_bounds H F μ hSeed hH3
      (activeRoot_of_positive_seed_degree hSeed v hdeg)).1
  · left
    have hd : (nbrsIn (edges H) v).card = 0 := by omega
    have hid := seed_star_identity H F μ hSeed v
    rw [hd, Nat.cast_zero] at hid
    linarith only [hid]

theorem starWeight_zero_of_zero_seed_degree {H : Host V I} {F : Set (Multiset I)}
    (v : V) (hdeg : (nbrsIn (edges H) v).card = 0) {T : Finset V}
    (hT : IsAllowed H F T) : starWeight v T = 0 := by
  by_contra hn
  have hv : v ∈ T := by
    by_contra hv
    exact hn (by simp only [starWeight, if_neg hv])
  obtain ⟨u, hu, huv⟩ := exists_mem_ne (by rw [hT.1]; norm_num : 1 < T.card) v
  have hadj := hT.2.1 v hv u hu huv.symm
  have huNbr : u ∈ nbrsIn (edges H) v := by
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨huv, mem_univ _⟩,
      by simpa [edges] using hadj⟩
  have hc := card_pos.mpr ⟨u, huNbr⟩
  omega

#print axioms activeRoot_of_positive_seed_degree
#print axioms positive_seed_degree_lower
#print axioms star_seed_mass_zero_or_lower
#print axioms starWeight_zero_of_zero_seed_degree
end TypedTriangle.Pasch
