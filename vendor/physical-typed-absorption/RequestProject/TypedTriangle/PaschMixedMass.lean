module
public import RequestProject.TypedTriangle.PaschMixedCompletions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

def mixedMass (A B : Finset (Finset V)) (μ : Finset V → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ S ∈ A.powersetCard ℓ, completionWeight B S * ∏ T ∈ S, μ T

def mixedDegree (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (ℓ : ℕ) (R : Finset (Finset V)) : ℝ :=
  ∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
    completionWeight B S * ∏ T ∈ S \ R, μ T

/-- Weighted fiber counting for the fixed bank. Each configuration contributes
once, indexed by its exact family of blocks outside B. -/
theorem completion_weighted_sum (A B : Finset (Finset V))
    (D : Finset (Finset (Finset V))) (hD : ∀ S ∈ D, S ⊆ A)
    (f : Finset (Finset V) → ℝ) :
    (∑ S ∈ D, completionWeight B S * f S) =
      ∑ K ∈ (configurations (A ∪ B)).filter (fun K => K \ B ∈ D), f (K \ B) := by
  let X := (configurations (A ∪ B)).filter (fun K => K \ B ∈ D)
  have hMap : (X : Set (Finset (Finset V))).MapsTo (fun K => K \ B) D :=
    fun K hK => (mem_filter.mp hK).2
  calc
    _ = ∑ S ∈ D, ∑ K ∈ X.filter (fun K => K \ B = S), f (K \ B) := by
      apply sum_congr rfl
      intro S hS
      have hFiber : X.filter (fun K => K \ B = S) =
          (configurations (S ∪ B)).filter (fun K => K \ B = S) := by
        calc
          _ = (configurations (A ∪ B)).filter (fun K => K \ B = S) := by
            ext K
            simp only [X, mem_filter]
            constructor
            · exact fun h => ⟨h.1.1, h.2⟩
            · intro h
              exact ⟨⟨h.1, h.2.symm ▸ hS⟩, h.2⟩
          _ = _ := completion_fiber_eq B A S (hD S hS)
      rw [hFiber]
      calc
        _ = ∑ _K ∈ (configurations (S ∪ B)).filter (fun K => K \ B = S), f S := by
          simp only [sum_const, nsmul_eq_mul, completionWeight, completionCount]
        _ = _ := sum_congr rfl (fun K hK => (congrArg f (mem_filter.mp hK).2).symm)
    _ = _ := sum_fiberwise_of_maps_to hMap (fun K => f (K \ B))

theorem mixedMass_eq_configuration_sum (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) :
    mixedMass A B μ ℓ =
      ∑ K ∈ (configurations (A ∪ B)).filter (fun K => K \ B ∈ A.powersetCard ℓ),
        ∏ T ∈ K \ B, μ T :=
  completion_weighted_sum A B (A.powersetCard ℓ)
    (fun S hS => (mem_powersetCard.mp hS).1) _

theorem mixedDegree_eq_configuration_sum (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (R : Finset (Finset V)) :
    mixedDegree A B μ ℓ R =
      ∑ K ∈ (configurations (A ∪ B)).filter
        (fun K => K \ B ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S)),
        ∏ T ∈ (K \ B) \ R, μ T :=
  completion_weighted_sum A B ((A.powersetCard ℓ).filter (fun S => R ⊆ S))
    (fun S hS => (mem_powersetCard.mp (mem_filter.mp hS).1).1) _

/-- A common bound for the remaining new blocks of each configuration.
Bank blocks are unweighted and fixed blocks contribute no coefficient. -/
theorem outside_product_sum_le (A B : Finset (Finset V))
    (D : Finset (Finset (Finset V))) (μ : Finset V → ℝ) (R : Finset (Finset V))
    (ℓ : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hD : ∀ K ∈ D, K \ B ⊆ A ∧ (K \ B).card = ℓ ∧ R ⊆ K \ B)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ b) :
    (∑ K ∈ D, ∏ T ∈ (K \ B) \ R, μ T) ≤ (D.card : ℝ) * b ^ (ℓ - R.card) := by
  calc
    _ ≤ ∑ _K ∈ D, b ^ (ℓ - R.card) := by
      apply sum_le_sum
      intro K hK
      obtain ⟨hSub, hCard, hR⟩ := hD K hK
      have hp := prod_le_prod₀
        (fun T (hT : T ∈ (K \ B) \ R) => hμ0 T (hSub (mem_sdiff.mp hT).1))
        (fun T (hT : T ∈ (K \ B) \ R) => hμb T (hSub (mem_sdiff.mp hT).1))
      simpa only [prod_const, card_sdiff_of_subset hR, hCard] using hp
    _ = _ := by rw [sum_const, nsmul_eq_mul]

#print axioms completion_weighted_sum
#print axioms mixedMass_eq_configuration_sum
#print axioms mixedDegree_eq_configuration_sum
#print axioms outside_product_sum_le
end TypedTriangle.Pasch
