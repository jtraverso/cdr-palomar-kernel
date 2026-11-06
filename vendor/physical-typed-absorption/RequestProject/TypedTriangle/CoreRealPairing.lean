/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreChargeCell
public import RequestProject.TypedTriangle.NativeSeedNibble
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CoreMonitor
open CorePayment
variable {V : Type*} [Fintype V]

/-- Sum transport for zero extension, including coefficients on edges that touch
the outside of the core. Such edges vanish because the PROFILE is zero there. -/
lemma sum_edgeZeroExtend {A : Type*} [AddCommMonoid A] (Z : Finset V)
    (x : Sym2 (Survivors Z) → ℤ) (f : Sym2 V → ℤ → A) (hf : ∀ e, f e 0 = 0) :
    (∑ e, f e (edgeZeroExtend Z x e)) =
      ∑ e, f (edgeLift Z e) (x e) := by
  let S : Finset (Sym2 V) := univ.filter fun e => ∀ v ∈ e, v ∉ Z
  have hs : (∑ e ∈ S, f e (edgeZeroExtend Z x e)) = ∑ e, f (edgeLift Z e) (x e) := by
    symm
    refine sum_bij (fun e _ => edgeLift Z e) ?_ ?_ ?_ ?_
    · intro e _
      exact mem_filter.mpr ⟨mem_univ _,fun v hv => by
        obtain ⟨w,_,rfl⟩ := Sym2.mem_map.mp hv
        exact w.2⟩
    · intro e _ e' _ he
      exact edgeLift_injective Z he
    · intro e he
      exact ⟨e.attachWith (mem_filter.mp he).2,mem_univ _,Sym2.attachWith_map_subtypeVal _⟩
    · intro e _
      dsimp only [edgeLift]
      rw [edgeZeroExtend_apply_map]
  rw [←hs]
  symm
  apply sum_subset (subset_univ _)
  intro e _ he
  have hav : ¬ ∀ v ∈ e, v ∉ Z := fun h => he (mem_filter.mpr ⟨mem_univ _,h⟩)
  push_neg at hav
  obtain ⟨v,hve,hv⟩ := hav
  rw [edgeZeroExtend_vanish Z x e ⟨v,hv,hve⟩,hf]

lemma pairing_zeroExtend (Z : Finset V) (x : Sym2 (Survivors Z) → ℤ) (lam : Sym2 V → ℝ) :
    (∑ e, lam e*(edgeZeroExtend Z x e:ℝ)) =
      ∑ e, lam (edgeLift Z e)*(x e:ℝ) :=
  sum_edgeZeroExtend Z x (fun e z => lam e*(z:ℝ)) (by simp)

def fallback (bad : Finset V) (lam0 : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  if ∀ v ∈ e, v ∉ bad then lam0 e else 0

def glued (Z bad : Finset V) (S : Set (Sym2 (Survivors Z)))
    (lamH p : Sym2 (Survivors Z) → ℝ) (lam0 : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  if he : ∀ v ∈ e, v ∉ Z then
    if e.attachWith he ∈ S then lamH (e.attachWith he)-p (e.attachWith he)
    else fallback bad lam0 e
  else fallback bad lam0 e

lemma glued_map (Z bad : Finset V) (S : Set (Sym2 (Survivors Z)))
    (lamH p : Sym2 (Survivors Z) → ℝ) (lam0 : Sym2 V → ℝ) (e : Sym2 (Survivors Z)) :
    glued Z bad S lamH p lam0 (edgeLift Z e) =
      if e ∈ S then lamH e-p e else fallback bad lam0 (edgeLift Z e) := by
  have he : ∀ v ∈ edgeLift Z e, v ∉ Z := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := Sym2.mem_map.mp hv
    exact w.2
  have heq : (edgeLift Z e).attachWith he = e := by
    apply Sym2.map.injective Subtype.val_injective
    exact Sym2.attachWith_map_subtypeVal he
  simp only [glued,dif_pos he,heq]

lemma glued_bound (Z bad : Finset V) (S : Set (Sym2 (Survivors Z)))
    (lamH p : Sym2 (Survivors Z) → ℝ) (lam0 : Sym2 V → ℝ)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hH : ∀ e, |lamH e| ≤ A) (hp : ∀ e, |p e| ≤ C) (h0 : ∀ e, |lam0 e| ≤ A) :
    ∀ e, |glued Z bad S lamH p lam0 e| ≤ A+C := by
  intro e
  unfold glued fallback
  split_ifs with he hs hb hb
  · exact (abs_sub _ _).trans (add_le_add (hH _) (hp _))
  · exact (h0 e).trans (le_add_of_nonneg_right hC)
  · simpa only [abs_zero] using add_nonneg hA hC
  · exact (h0 e).trans (le_add_of_nonneg_right hC)
  · simpa only [abs_zero] using add_nonneg hA hC

/-- Exact agreement away from the saturated set. On core edges the agreement
is a matching-potential identity; it is never obtained by zero-filling them. -/
lemma glued_agrees_away (Z bad : Finset V) (S : Set (Sym2 (Survivors Z)))
    (lamH p : Sym2 (Survivors Z) → ℝ) (lam0 : Sym2 V → ℝ)
    (hmatch : ∀ e ∈ S, (∀ v ∈ edgeLift Z e, v ∉ bad) → lamH e-p e=lam0 (edgeLift Z e))
    (e : Sym2 V) (he : ∀ v ∈ e, v ∉ bad) : glued Z bad S lamH p lam0 e = lam0 e := by
  unfold glued
  split_ifs with hz hs
  · have hh := hmatch (e.attachWith hz) hs (by simpa only [edgeLift,Sym2.attachWith_map_subtypeVal] using he)
    simpa only [edgeLift,Sym2.attachWith_map_subtypeVal] using hh
  · exact if_pos he
  · exact if_pos he

lemma glued_pairing (Z bad : Finset V) (S : Set (Sym2 (Survivors Z)))
    (lamH p : Sym2 (Survivors Z) → ℝ) (lam0 : Sym2 V → ℝ)
    (x : Sym2 (Survivors Z) → ℤ) (hsupp : ∀ e, e ∉ S → x e = 0)
    (hkill : ∑ e, p e*(x e:ℝ)=0) :
    (∑ e, glued Z bad S lamH p lam0 e*(edgeZeroExtend Z x e:ℝ)) =
      ∑ e, lamH e*(x e:ℝ) := by
  rw [pairing_zeroExtend]
  have heq : (∑ e, glued Z bad S lamH p lam0 (edgeLift Z e)*(x e:ℝ)) =
      ∑ e, (lamH e-p e)*(x e:ℝ) := by
    apply sum_congr rfl
    intro e _
    rw [glued_map]
    by_cases he : e ∈ S
    · rw [if_pos he]
    · rw [if_neg he,hsupp e he]
      simp
  rw [heq]
  simp_rw [sub_mul]
  rw [sum_sub_distrib,hkill,sub_zero]

lemma triangle_monitor_bound (lam : Sym2 V → ℝ) (bad : Finset V) (L : ℝ) (hL : 0 ≤ L)
    (hlam : ∀ e, |lam e| ≤ L) (T : Finset V) (hT : T.card=3)
    (hvanish : Disjoint T bad → ∑ e ∈ triEdges T, lam e = 0) :
    |∑ e ∈ triEdges T, lam e| ≤ 3*L*(T∩bad).card := by
  by_cases hd : Disjoint T bad
  · rw [hvanish hd,abs_zero]
    positivity
  · have hc : (1:ℝ) ≤ (T∩bad).card := by
      have hh : 0 < (T∩bad).card := card_pos.mpr (nonempty_iff_ne_empty.mpr (by
        intro he
        exact hd (disjoint_iff_inter_eq_empty.mpr he)))
      exact_mod_cast hh
    have h3 : (triEdges T).card = 3 := by
      rw [←NativeNibble.nibble_triEdges_eq]
      exact PartitionedTriangleAbsorption.Nibble.card_triEdges hT
    calc |∑ e ∈ triEdges T, lam e| ≤ ∑ e ∈ triEdges T, |lam e| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ triEdges T, L := sum_le_sum fun e _ => hlam e
      _ = 3*L := by rw [sum_const,h3]; simp [nsmul_eq_mul]
      _ ≤ 3*L*(T∩bad).card := le_mul_of_one_le_right (by positivity) hc
end TypedTriangle.CoreMonitor
