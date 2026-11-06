module
public import RequestProject.TypedTriangle.PaschSupersaturation
public import RequestProject.TypedTriangle.Packing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- An exact seed cannot have an empty triangle domain at an existing edge. -/
theorem allowed_nonempty_of_edges {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hE : (edges H).Nonempty) : (allowed H F).Nonempty := by
  obtain ⟨e,he⟩ := hE
  have heG : e ∈ H.G.edgeSet := (mem_filter.mp he).2
  by_contra hEmpty
  have hz : allowed H F = ∅ := not_nonempty_iff_eq_empty.mp hEmpty
  have hLoad := hH1.2 e heG
  rw [hz] at hLoad
  simp only [filter_empty,sum_empty] at hLoad
  norm_num at hLoad

theorem exists_allowed_root_of_edges {H : Host V I} {F : Set (Multiset I)}
    {C : ℝ} {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hE : (edges H).Nonempty) : ∃ a b c : V, IsAllowed H F {a,b,c} := by
  obtain ⟨T,hT⟩ := allowed_nonempty_of_edges hH1 hE
  have hAllow := isAllowed_of_mem_allowed hT
  obtain ⟨a,b,c,_,_,_,hSet⟩ := card_eq_three.mp hAllow.1
  refine ⟨a,b,c,?_⟩
  simpa only [hSet] using hAllow

theorem allowed_empty_of_edges_empty {H : Host V I} {F : Set (Multiset I)}
    (hE : edges H = ∅) : allowed H F = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro T hT
  have hAllow := isAllowed_of_mem_allowed hT
  obtain ⟨a,b,c,hab,_,_,hSet⟩ := card_eq_three.mp hAllow.1
  have hAB : s(a,b) ∈ triEdges T := mem_triEdges.mpr
    ⟨by simp [hSet],by simp [hSet],hab⟩
  have he := triEdges_subset_edges hAllow hAB
  rw [hE] at he
  exact notMem_empty _ he

theorem target_zero_of_edges_empty {H : Host V I} {F : Set (Multiset I)}
    (hE : edges H = ∅) (μ : Finset V → ℝ) : target μ (allowed H F) = 0 := by
  have hp : (∅ : Finset (Finset V)).powersetCard 4 = ∅ :=
    powersetCard_eq_empty.mpr (by simp)
  rw [allowed_empty_of_edges_empty hE,target,statistic_eq_sum]
  simp only [configurations,hp,filter_empty,sum_empty]

/-- H1 and H3 discharge the allowed-root witness in the nonempty branch.
There is no extra density or Pasch-mass hypothesis. -/
theorem target_lower_or_empty {H : Host V I} {F : Set (Multiset I)}
    {α C : ℝ} {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 0 < C)
    (hN : supersaturationOrder α ≤ Fintype.card V) :
    edges H = ∅ ∨ massConstant α C * (Fintype.card V : ℝ)^2 ≤ target μ (allowed H F) := by
  by_cases hE : edges H = ∅
  · exact Or.inl hE
  · obtain ⟨a,b,c,hT⟩ := exists_allowed_root_of_edges hH1 (nonempty_iff_ne_empty.mpr hE)
    exact Or.inr (target_lower_of_seed_and_common_neighbors hH1 hH3 hα hC hN hT)

#print axioms allowed_nonempty_of_edges
#print axioms exists_allowed_root_of_edges
#print axioms allowed_empty_of_edges_empty
#print axioms target_zero_of_edges_empty
#print axioms target_lower_or_empty
end TypedTriangle.Pasch
