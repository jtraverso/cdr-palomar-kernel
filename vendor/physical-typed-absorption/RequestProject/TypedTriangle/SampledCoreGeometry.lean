/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07.HingeCore
public import RequestProject.TypedTriangle.CorePoolGeometry
public import RequestProject.TypedTriangle.RestrictedHingeGeometry
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CorePaid
open S07V24
variable {V I : Type*} [Fintype V]

/-- The SAME sampled pools and hinge counts imply H3/H4 on the true core.
The positive geometry parameter is fixed from alpha,q,h, not from the host.
No large-complement deletion estimate is used for the small sampled core. -/
theorem sampled_core_geometry (H : Host V I) (F : Set (Multiset I))
    {α q : ℝ} {h : ℕ} (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h)
    (hH4 : HingeCond H F α h) (W : Finset V)
    (hpool : ∀ u v, u ≠ v → ∀ k, ({H.lab u,H.lab v,k}:Multiset I) ∈ F →
      q*α*Fintype.card V/2 ≤ ((commonNbrs H k u v)∩W).card)
    (hhinge : ∀ u v a b, HingeTest H.G H.lab F u v a b →
      α*q^(hOrd hH4 u v a b-4)*(Fintype.card V:ℝ)^(hOrd hH4 u v a b-4)/2 ≤
        ((SparseEdge.hinges H.G H.lab F u v a b (hOrd hH4 u v a b)).filter
          (fun J => freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ\W)) F (α*q^h/2) ∧
      HingeCond (restrictedHost H (univ\W)) F (α*q^h/2) h := by
  have hβ : 0 ≤ α*q^h/2 := by positivity
  have hpow1 : q^h ≤ q := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hq.le hq1 (show 1 ≤ h by omega))
  refine ⟨commonNbrCond_of_core_pool H F W hβ ?_,?_⟩
  · intro u v huv k hk
    exact (show α*q^h/2*Fintype.card V ≤ q*α*Fintype.card V/2 by
      nlinarith only [mul_le_mul_of_nonneg_left hpow1
        (show 0 ≤ α*(Fintype.card V:ℝ) by positivity)]).trans (hpool u v huv k hk)
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
    have hi6 : 6 ≤ i := hs.1
    have hih : i ≤ h := hs.2.1
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
    have hN : (Fintype.card (Survivors (univ\W)):ℝ) ≤ Fintype.card V := by
      exact_mod_cast (Fintype.card_subtype_le (fun x : V => x ∉ univ\W))
    have hpow : q^h ≤ q^(i-4) := pow_le_pow_of_le_one hq.le hq1 (by omega)
    refine ⟨i,hi6,hih,?_⟩
    calc
      α*q^h/2*(Fintype.card (Survivors (univ\W)):ℝ)^(i-4)
          ≤ α*q^h/2*(Fintype.card V:ℝ)^(i-4) := by gcongr
      _ ≤ α*q^(i-4)*(Fintype.card V:ℝ)^(i-4)/2 := by
        have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hα.le)
          (show (0:ℝ) ≤ (Fintype.card V:ℝ)^(i-4) by positivity)
        nlinarith only [hp]
      _ ≤ ((SparseEdge.hinges H.G H.lab F u.1 v.1 a.1 b.1 i).filter
          (fun J => freeV u.1 v.1 a.1 b.1 J ⊆ W)).card := hhinge u.1 v.1 a.1 b.1 ht
      _ ≤ (hinges (restrictedHost H (univ\W)) F u v a b i).card := by exact_mod_cast hCount

end TypedTriangle.CorePaid
