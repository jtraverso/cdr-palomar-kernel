/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SampledCoreGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open S07V24
variable {V I : Type*} [Fintype V]

/-- Counts are normalized by the ACTUAL child order. No ambient-order loss
is introduced when transporting pools or hinges to the child vertex type. -/
theorem core_geometry_of_child_counts (H : Host V I) (F : Set (Multiset I))
    {α κ : ℝ} {h : ℕ} (hH4 : HingeCond H F α h) (W : Finset V)
    (hpool : ∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      κ*W.card ≤ ((commonNbrs H k u v)∩W).card)
    (hhinge : ∀ u v a b, HingeTest H.G H.lab F u v a b →
      κ*(W.card:ℝ)^(hOrd hH4 u v a b-4) ≤
        ((SparseEdge.hinges H.G H.lab F u v a b (hOrd hH4 u v a b)).filter
          (fun J => freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ\W)) F κ ∧
      HingeCond (restrictedHost H (univ\W)) F κ h := by
  constructor
  · intro u v huv k hk
    have heq : ((commonNbrs H k u.1 v.1).filter (fun w => w ∉ univ\W)) =
        commonNbrs H k u.1 v.1 ∩ W := by ext w; simp
    rw [card_commonNbrs_restrictedHost,heq,card_survivors_compl]
    exact hpool u.1 v.1 (fun he => huv (Subtype.ext he)) k hk
  · intro u v a b hab hTa hTb
    have hTa' : IsAllowed H F {u.1,v.1,a.1} := by
      apply (isAllowed_restricted_triple H F (univ\W) u v a).mp
      convert hTa using 1 <;> ext x <;> simp
    have hTb' : IsAllowed H F {u.1,v.1,b.1} := by
      apply (isAllowed_restricted_triple H F (univ\W) u v b).mp
      convert hTb using 1 <;> ext x <;> simp
    have ht : HingeTest H.G H.lab F u.1 v.1 a.1 b.1 :=
      ⟨fun he => hab (Subtype.ext he),hTa',hTb'⟩
    have hs := hOrd_spec hH4 ht
    let i := hOrd hH4 u.1 v.1 a.1 b.1
    have hroot : ({u.1,v.1,a.1,b.1}:Finset V) ⊆ W := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simpa only [mem_sdiff,mem_univ,true_and,not_not] using u.2
      · simpa only [mem_sdiff,mem_univ,true_and,not_not] using v.2
      · simpa only [mem_sdiff,mem_univ,true_and,not_not] using a.2
      · simpa only [mem_sdiff,mem_univ,true_and,not_not] using b.2
    have hSub : ((SparseEdge.hinges H.G H.lab F u.1 v.1 a.1 b.1 i).filter
        (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ W)) ⊆
        (hinges H F u.1 v.1 a.1 b.1 i).filter (fun J => Disjoint (support J) (univ\W)) := by
      intro J hJ
      obtain ⟨hJ,hFree⟩ := mem_filter.mp hJ
      refine mem_filter.mpr ⟨hJ,disjoint_left.mpr ?_⟩
      intro x hx hxOut
      have hxW : x ∈ W := by
        by_cases hr : x ∈ ({u.1,v.1,a.1,b.1}:Finset V)
        · exact hroot hr
        · exact hFree (mem_sdiff.mpr ⟨hx,hr⟩)
      exact (mem_sdiff.mp hxOut).2 hxW
    have hCount := (card_le_card hSub).trans
      (surviving_hinges_card_le H F (univ\W) u v a b i hTa' hTb')
    refine ⟨i,hs.1,hs.2.1,?_⟩
    rw [card_survivors_compl]
    exact (hhinge u.1 v.1 a.1 b.1 ht).trans (by exact_mod_cast hCount)

/-- A sampled child of size at most `r*q*n` inherits geometry `c*alpha/r^h`.
In particular the geometry constant has NO dependence on the sampling fraction
`q`. The retained proportion `c` and size slack `r` remain explicit, so an
iterated argument can use summable losses rather than a fixed factor per layer. -/
theorem sampled_core_geometry_scaled (H : Host V I) (F : Set (Multiset I))
    {α q c r : ℝ} {h : ℕ} (hα : 0 < α) (hq : 0 < q) (hc : 0 < c)
    (hr : 1 ≤ r) (hh : 1 ≤ h) (hH4 : HingeCond H F α h) (W : Finset V)
    (hW : (W.card:ℝ) ≤ r*q*Fintype.card V)
    (hpool : ∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      c*α*q*Fintype.card V ≤ ((commonNbrs H k u v)∩W).card)
    (hhinge : ∀ u v a b, HingeTest H.G H.lab F u v a b →
      c*α*q^(hOrd hH4 u v a b-4)*(Fintype.card V:ℝ)^(hOrd hH4 u v a b-4) ≤
        ((SparseEdge.hinges H.G H.lab F u v a b (hOrd hH4 u v a b)).filter
          (fun J => freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ\W)) F (c*α/r^h) ∧
      HingeCond (restrictedHost H (univ\W)) F (c*α/r^h) h := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hnum : ∀ d : ℕ, d ≤ h →
      c*α/r^h*(W.card:ℝ)^d ≤ c*α*q^d*(Fintype.card V:ℝ)^d := by
    intro d hd
    have hpow : r^d ≤ r^h := pow_le_pow_right₀ hr hd
    calc
      c*α/r^h*(W.card:ℝ)^d ≤ c*α/r^h*(r*q*Fintype.card V)^d := by gcongr
      _ = c*α/r^h*r^d*q^d*(Fintype.card V:ℝ)^d := by rw [mul_pow,mul_pow]; ring
      _ ≤ c*α/r^h*r^h*q^d*(Fintype.card V:ℝ)^d := by gcongr
      _ = c*α*q^d*(Fintype.card V:ℝ)^d := by field_simp
  apply core_geometry_of_child_counts H F hH4 W
  · intro u v huv k hk
    have hn := hnum 1 hh
    simp only [pow_one] at hn
    exact hn.trans (hpool u v huv k hk)
  · intro u v a b ht
    exact (hnum _ (by have := (hOrd_spec hH4 ht).2.1; omega)).trans
      (hhinge u v a b ht)

end TypedTriangle.CorePaid
