/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeWeightedPacking
public import RequestProject.TypedTriangle.NativeDegree
public import RequestProject.TypedTriangle.Monitor
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedStar
variable {V I : Type*} [Fintype V]

def ActiveRoot (H : Host V I) (F : Set (Multiset I)) (v : V) : Prop :=
  ∃ T, IsAllowed H F T ∧ v ∈ T

def starWeight (v : V) (T : Finset V) : ℝ := if v ∈ T then 1 else 0

lemma active_degree_lower {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) {v : V} (hv : ActiveRoot H F v) :
    α*Fintype.card V ≤ (nbrsIn (edges H) v).card := by
  obtain ⟨T,hT,hv⟩ := hv
  obtain ⟨u,hu,huv⟩ := exists_mem_ne (by rw [hT.1]; norm_num : 1 < T.card) v
  obtain ⟨w,hwv,hwu,rfl⟩ := ActiveCover.allowed_eq_triple hT.1 hv hu huv.symm
  have hlink : (linkGraph H F v).Adj u w := ⟨hwu.symm,hT⟩
  have hmin := link_minDeg h3 hlink
  have hsub : univ.filter ((linkGraph H F v).Adj u) ⊆ nbrsIn (edges H) v := by
    intro z hz
    have hh := (mem_filter.mp hz).2
    have hne := linkGraph_adj_ne hh
    refine mem_filter.mpr ⟨mem_erase.mpr ⟨hne.2.1.symm,mem_univ _⟩,?_⟩
    have ha := hh.2.2.1 v (by simp) z (by simp) hne.2.1
    simpa [edges] using ha
  exact hmin.trans (by exact_mod_cast card_le_card hsub)

lemma seed_star_identity (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    {C : ℝ} (hφ : IsDiffuseSeed H F C φ) (v : V) :
    2*(∑ T ∈ allowed H F, φ T*starWeight v T) = (nbrsIn (edges H) v).card := by
  have hload : ∀ e ∈ edges H, bdry H F φ e = 1 := by
    intro e he
    rw [bdry_eq_sum_triOn]
    exact hφ.2 e (mem_filter.mp he).2
  simpa only [triAt,sum_filter,starWeight,mul_ite,mul_one,mul_zero] using seed_star_sum hload v

lemma seed_star_mass_bounds (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    {C α : ℝ} (hφ : IsDiffuseSeed H F C φ) (h3 : CommonNbrCond H F α)
    {v : V} (hv : ActiveRoot H F v) :
    α/2*Fintype.card V ≤ (∑ T ∈ allowed H F, φ T*starWeight v T) ∧
      (∑ T ∈ allowed H F, φ T*starWeight v T) ≤ Fintype.card V/2 := by
  have hs := seed_star_identity H F φ hφ v
  have hl := active_degree_lower h3 hv
  have hu : ((nbrsIn (edges H) v).card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ _
  constructor <;> linarith

lemma incident_card_eq_nbrs (E : Finset (Sym2 V)) (v : V)
    (hE : ∀ e ∈ E, ¬e.IsDiag) :
    (E.filter (fun e => v ∈ e)).card = (nbrsIn E v).card := by
  symm
  apply card_bij (fun w _ => s(v,w))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2,by simp⟩
  · intro w _ w' _ he
    rcases Sym2.eq_iff.mp he with ⟨_,hh⟩ | ⟨h₁,h₂⟩
    · exact hh
    · exact h₂.trans h₁
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    have hd := hE e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using hd
      have hv' : v=a ∨ v=b := by simpa using hv
      rcases hv' with rfl | rfl
      · exact ⟨b,mem_filter.mpr ⟨mem_erase.mpr ⟨hab.symm,mem_univ _⟩,he⟩,rfl⟩
      · exact ⟨a,mem_filter.mpr ⟨mem_erase.mpr ⟨hab,mem_univ _⟩,by simpa only [Sym2.eq_swap] using he⟩,Sym2.eq_swap⟩

lemma sparse_leftover_of_star_tests (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) {C η : ℝ} (hφ : IsDiffuseSeed H F C φ) (hη : 0 ≤ η)
    (P : Finset (Finset V)) (hP : IsPacking H F P)
    (hstar : ∀ v, |(∑ T ∈ P, starWeight v T)-(∑ T ∈ allowed H F, φ T*starWeight v T)| ≤
      η*(∑ T ∈ allowed H F, φ T*starWeight v T)) :
    ∀ v, (((edges H \ P.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V := by
  intro v
  have hPE : P.biUnion triEdges ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hP.1 T hT) heT
  have hsub : nbrsIn (P.biUnion triEdges) v ⊆ nbrsIn (edges H) v := by
    intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).1,hPE (mem_filter.mp hw).2⟩
  have hd : nbrsIn (edges H \ P.biUnion triEdges) v = nbrsIn (edges H) v \ nbrsIn (P.biUnion triEdges) v := by
    ext w
    simp only [nbrsIn,mem_filter,mem_sdiff]
    tauto
  have hloop : ∀ e ∈ edges H \ P.biUnion triEdges, ¬e.IsDiag := by
    intro e he
    have hh := (mem_filter.mp (mem_sdiff.mp he).1).2
    exact H.G.not_isDiag_of_mem_edgeSet hh
  rw [incident_card_eq_nbrs _ v hloop,hd,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub)]
  have hc := packing_star_count hP v
  have hcR : ((nbrsIn (P.biUnion triEdges) v).card:ℝ) = 2*(∑ T ∈ P, starWeight v T) := by
    rw [←hc]
    push_cast
    simp [starWeight,sum_filter]
  have hs := seed_star_identity H F φ hφ v
  have hbound : ((nbrsIn (edges H) v).card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ _
  have herr := (le_abs_self _).trans (hstar v)
  have herr' := (neg_le_abs _).trans (hstar v)
  have hmul := mul_le_mul_of_nonneg_left hbound hη
  rw [hcR]
  nlinarith
end TypedTriangle.WeightedStar
