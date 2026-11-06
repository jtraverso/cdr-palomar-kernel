module
public import RequestProject.TypedTriangle.ClonedTupleEGJ
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.WeightedClone
variable {E ι : Type*} [Fintype E] [Fintype ι]

def linearTupleWeight (a : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, a i

theorem baseMatching_singleton (P : ι → Finset E) (i : ι) : BaseMatching P {i} := by
  intro x hx y hy hxy
  have hx' := mem_singleton.mp hx
  have hy' := mem_singleton.mp hy
  exact False.elim (hxy (hx'.trans hy'.symm))

theorem tupleMass_linear (P : ι → Finset E) (m : ι → ℕ) (a : ι → ℝ) :
    tupleMass P m (linearTupleWeight a) 1 = ∑ i, (m i : ℝ) * a i := by
  simp only [tupleMass, sum_filter, powersetCard_one, sum_map]
  simp only [Function.Embedding.coeFn_mk, baseMatching_singleton, if_pos,
    linearTupleWeight, sum_singleton, prod_singleton, mul_comm]

theorem tupleExtensionMass_linear_singleton (P : ι → Finset E) (m : ι → ℕ)
    (a : ι → ℝ) (i : ι) : tupleExtensionMass P m (linearTupleWeight a) 1 {i} = a i := by
  have hFilter : ((univ : Finset ι).powersetCard 1).filter
      (fun S => ({i} : Finset ι) ⊆ S ∧ BaseMatching P S) = {{i}} := by
    ext S
    simp only [mem_filter, mem_powersetCard, mem_singleton]
    constructor
    · intro h
      exact (eq_of_subset_of_card_le h.2.1 (by rw [h.1.2]; simp only [card_singleton]; omega)).symm
    · intro h
      subst S
      exact ⟨⟨subset_univ _, card_singleton i⟩, subset_refl _, baseMatching_singleton P i⟩
  unfold tupleExtensionMass
  rw [hFilter, sum_singleton, sdiff_self]
  simp [linearTupleWeight]

theorem statistic_linear (a : ι → ℝ) (D : Finset ι) :
    PatternStatistics.statistic (linearTupleWeight a) 1 D = ∑ i ∈ D, a i := by
  simp only [PatternStatistics.statistic, powersetCard_one, sum_map,
    Function.Embedding.coeFn_mk, linearTupleWeight, sum_singleton]

#print axioms tupleMass_linear
#print axioms tupleExtensionMass_linear_singleton
#print axioms statistic_linear
end TypedTriangle.WeightedClone
