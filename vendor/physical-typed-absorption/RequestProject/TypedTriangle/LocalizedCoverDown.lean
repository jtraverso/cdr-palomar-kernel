/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.WeightedStars
public import RequestProject.TypedTriangle.CoverDownProtected
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.LocalizedCover
variable {V I : Type*} [Fintype V]

def edgeSum (lam : Sym2 V → ℝ) (S : Finset (Sym2 V)) : ℝ := ∑ e ∈ S, lam e
def triSum (lam : Sym2 V → ℝ) (T : Finset V) : ℝ := edgeSum lam (triEdges T)

lemma edgeSum_eq_pairing (lam : Sym2 V → ℝ) (S : Finset (Sym2 V)) :
    edgeSum lam S = ∑ e, lam e*indR S e := by
  simp [edgeSum,indR,mul_ite]

/-- Pairing an actual packing equals summing its triangular monitor. -/
theorem packing_edge_sum_eq {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (lam : Sym2 V → ℝ) :
    edgeSum lam (P.biUnion triEdges) = ∑ T ∈ P, triSum lam T := by
  rw [edgeSum_eq_pairing]
  simp_rw [←sum_indR_of_isDecomposition hP.isDecomposition]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  exact (edgeSum_eq_pairing lam (triEdges T)).symm

/-- The actual unused reserve satisfies L-X = U-boundary(Pcov), coordinate by
coordinate. This retains the full reserve X, rather than calling L sublinear. -/
theorem cover_down_indicator_difference (U X E : Finset (Sym2 V))
    (hUX : Disjoint U X) (hU : U ⊆ E) (hE : E ⊆ U∪X) :
    indR (X\E)-indR X = indR U-indR E := by
  funext e
  have h₁ := fun he : e ∈ U => hU he
  have h₂ := fun he : e ∈ E => hE he
  have h₃ := fun hu : e ∈ U => fun hx : e ∈ X => disjoint_left.mp hUX hu hx
  by_cases hu : e ∈ U <;> by_cases hx : e ∈ X <;> by_cases he : e ∈ E <;>
    simp_all [indR]

theorem cover_down_moment_identity {H : Host V I} {F : Set (Multiset I)}
    (U X : Finset (Sym2 V)) (P : Finset (Finset V)) (hP : IsPacking H F P)
    (hUX : Disjoint U X) (hU : U ⊆ P.biUnion triEdges)
    (hE : P.biUnion triEdges ⊆ U∪X) (lam : Sym2 V → ℝ) :
    edgeSum lam (X\P.biUnion triEdges)-edgeSum lam X =
      edgeSum lam U-∑ T ∈ P, triSum lam T := by
  have hid := cover_down_indicator_difference U X (P.biUnion triEdges) hUX hU hE
  have hpair := congrArg (fun x : Sym2 V → ℝ => ∑ e, lam e*x e) hid
  simp only [Pi.sub_apply,mul_sub,sum_sub_distrib] at hpair
  simp_rw [←edgeSum_eq_pairing] at hpair
  rw [packing_edge_sum_eq hP] at hpair
  exact hpair

/-- Localized loss of a cover-down packing, using the existing packing monitor
theorem. Only triangles meeting bad can contribute; maximum degree pays their
total load. No density or size bound on the leftover reserve X is needed. -/
theorem packing_localized_bound {H : Host V I} {F : Set (Multiset I)}
    {P : Finset (Finset V)} (hP : IsPacking H F P) (D L : ℝ) (hL : 0 ≤ L)
    (hD : ∀ v, (((P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ D)
    (bad : Finset V) (lam : Sym2 V → ℝ)
    (htri : ∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) :
    |∑ T ∈ P, triSum lam T| ≤ (3*L*bad.card)*D/2 := by
  let a : V → ℝ := fun v => if v ∈ bad then 3*L else 0
  have ha : ∀ v, 0 ≤ a v := by intro v; dsimp [a]; split_ifs <;> positivity
  have hsum : ∑ v, a v = 3*L*bad.card := by simp [a,mul_comm]
  have hTsum : ∀ T : Finset V, ∑ v ∈ T, a v = 3*L*(T∩bad).card := by
    intro T
    simp [a,sum_ite_mem,inter_comm,mul_comm]
  have hD' : ∀ v, ((nbrsIn (P.biUnion triEdges) v).card:ℝ) ≤ D := by
    intro v
    have hdiag : ∀ e ∈ P.biUnion triEdges, ¬e.IsDiag := by
      intro e he
      obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
      exact H.G.not_isDiag_of_mem_edgeSet ((mem_filter.mp (triEdges_subset_edges (hP.1 T hT) heT)).2)
    rw [←WeightedStar.incident_card_eq_nbrs _ v hdiag]
    exact hD v
  have hh := packing_monitor_bound hP D hD' (triSum lam) a ha
    (fun T hT => by rw [hTsum]; exact htri T (hP.1 T hT))
  rw [hsum] at hh
  exact (abs_sum_le_sum_abs _ _).trans hh

/-- The moment of L-X is controlled by the monitored nibble remainder U and a
localized cover-down loss. The construction cannot silently drop the X term. -/
theorem localized_cover_down_entry {H : Host V I} {F : Set (Multiset I)}
    (U X : Finset (Sym2 V)) (P : Finset (Finset V)) (hP : IsPacking H F P)
    (hUX : Disjoint U X) (hU : U ⊆ P.biUnion triEdges)
    (hE : P.biUnion triEdges ⊆ U∪X) (D L E0 : ℝ) (hL : 0 ≤ L)
    (hD : ∀ v, (((P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ D)
    (bad : Finset V) (lam : Sym2 V → ℝ)
    (htri : ∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card)
    (hUmon : |edgeSum lam U| ≤ E0) :
    |edgeSum lam (X\P.biUnion triEdges)-edgeSum lam X| ≤ E0+(3*L*bad.card)*D/2 := by
  rw [cover_down_moment_identity U X P hP hUX hU hE lam]
  have hp := packing_localized_bound hP D L hL hD bad lam htri
  have hh := abs_add_le (edgeSum lam U) (-(∑ T ∈ P, triSum lam T))
  simp only [abs_neg,←sub_eq_add_neg] at hh
  exact hh.trans (add_le_add hUmon hp)
end TypedTriangle.LocalizedCover
