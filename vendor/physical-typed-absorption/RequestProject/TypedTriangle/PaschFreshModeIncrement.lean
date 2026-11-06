module
public import RequestProject.TypedTriangle.PaschSupportLedger
public import RequestProject.TypedTriangle.PaschFreshAbsorber
public import RequestProject.TypedTriangle.PaschPotentialIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- A triangle inside the cell edge set is supported on the cell vertices. -/
theorem triangle_subset_of_inside_edges {H : Host V I} {F : Set (Multiset I)}
    {T U : Finset V} {E : Finset (Sym2 V)} (hT : IsAllowed H F T)
    (hTE : triEdges T ⊆ E) (hInside : Inside U E) : T ⊆ U := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne (by rw [hT.1]; norm_num : 1 < T.card) x
  have he : s(x,y) ∈ triEdges T := mem_triEdges.mpr ⟨hx, hy, hyx.symm⟩
  exact hInside _ (hTE he) x (by simp)

/-- Freshness and a triangle-free input force every allowed mode block to be
among the new support triples already charged by the support ledger. -/
theorem fresh_mode_cost_le_support_increment {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U0 U : Finset V}
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle H F P)
    (hInside : Inside U (A ∪ P)) (R N : Finset (Finset V))
    (hN : ∀ T ∈ N, IsAllowed H F T ∧ triEdges T ⊆ A ∪ P) :
    (∑ T ∈ N, rootedCount (insert T R) T) ≤ supportIncrementCost R U0 U := by
  apply sum_le_sum_of_subset
  intro T hT
  obtain ⟨hAllowed, hEdges⟩ := hN T hT
  have hTU := triangle_subset_of_inside_edges hAllowed hEdges hInside
  have hNew : ¬ T ⊆ U0 := by
    obtain ⟨v, hv, hv0⟩ := allowed_triangle_meets_outside_of_fresh hFresh hFree hAllowed hEdges
    exact fun h => hv0 (h hv)
  exact mem_filter.mpr ⟨mem_powersetCard.mpr
    ⟨hTU.trans subset_union_right, hAllowed.1⟩, hNew⟩

theorem fresh_mode_count_increment_le {H : Host V I} {F : Set (Multiset I)}
    {A P : Finset (Sym2 V)} {U0 U : Finset V}
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle H F P)
    (hInside : Inside U (A ∪ P)) (R N : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (hNR : Disjoint N R)
    (hN : ∀ T ∈ N, IsAllowed H F T ∧ triEdges T ⊆ A ∪ P) :
    count (N ∪ R) ≤ count R + supportIncrementCost R U0 U +
      9*L*(N.card.choose 2) + N.card.choose 3 + N.card.choose 4 := by
  have hCount := count_union_le_potential_increment hL N hNR
  have hSupport := fresh_mode_cost_le_support_increment hFresh hFree hInside R N hN
  omega

#print axioms triangle_subset_of_inside_edges
#print axioms fresh_mode_cost_le_support_increment
#print axioms fresh_mode_count_increment_le
end TypedTriangle.Pasch
