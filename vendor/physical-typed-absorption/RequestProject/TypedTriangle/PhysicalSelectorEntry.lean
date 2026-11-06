/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V27.SelectorNative
public import RequestProject.TypedTriangle.Lattice
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section

/-! Physical integer demands satisfy the actual PAR/BAL admissibility
predicate of V27. No extra parity, balance or density assumption is added. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.SelectorEntry
open ComponentRows SignedCover S07V25 S07V27
variable {V I : Type*} [Fintype V]

def rowCharge (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (x : Sym2 V → ℤ) (v : V) (C : Finset V) : ℤ :=
  ∑ u, if comp G lab F v u = C then sgn (sigma G lab F (v,C) u) * x s(v,u) else 0

theorem physical_row_constraints {H : Host V I} {F : Set (Multiset I)}
    {x : Sym2 V → ℤ} (hx : x ∈ lattice H F) (v : V) (C : Finset V) :
    (IsBip H.G H.lab F (v,C) → rowCharge H.G H.lab F x v C = 0) ∧
      2 ∣ rowCharge H.G H.lab F x v C := by
  have hlocal := lattice_le_localGroup H F hx
  obtain ⟨c,hc⟩ := hlocal.2 v
  have hs := star_eq_sum_tri H.G H.lab F x hlocal.1 v C c hc
  change rowCharge H.G H.lab F x v C = _ at hs
  rw [hs]
  exact ⟨fun hb => sum_eq_zero fun T hT => by
      rw [(triVal_spec H.G H.lab F v C hT).1 hb,mul_zero],
    Finset.dvd_sum fun T hT => dvd_mul_of_dvd_right (triVal_spec H.G H.lab F v C hT).2 _⟩

lemma mem_component_iff {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {v u : V} {C : Finset V} (hC : C ∈ activeComps G lab F v) :
    u ∈ C ↔ comp G lab F v u = C := by
  obtain ⟨a,_,rfl⟩ := mem_activeComps.mp hC
  constructor
  · exact comp_eq_of_mem
  · intro h
    rw [← h]
    simp [comp]

lemma rowCharge_ind_eq_demand {H : Host V I} {F : Set (Multiset I)}
    (X : SimpleGraph V) [DecidableRel X.Adj] {L : Finset (Sym2 V)}
    (hL : L ⊆ X.edgeFinset) (v : V) {C : Finset V}
    (hC : C ∈ activeComps H.G H.lab F v) :
    rowCharge H.G H.lab F (ind L) v C =
      ∑ u ∈ SelSimul.demand X L v ∩ (X.neighborFinset v ∩ C),
        sgn (sigma H.G H.lab F (v,C) u) := by
  let S := SelSimul.demand X L v ∩ (X.neighborFinset v ∩ C)
  have hS : S = univ.filter (fun u => comp H.G H.lab F v u = C ∧ s(v,u) ∈ L) := by
    ext u
    simp only [S,SelSimul.demand,mem_inter,mem_filter,SimpleGraph.mem_neighborFinset,
      mem_univ,true_and]
    constructor
    · rintro ⟨⟨_,he⟩,_,hu⟩
      exact ⟨mem_component_iff hC |>.mp hu,he⟩
    · rintro ⟨hu,he⟩
      have ha : X.Adj v u := by simpa using hL he
      exact ⟨⟨ha,he⟩,ha,mem_component_iff hC |>.mpr hu⟩
  change _ = ∑ u ∈ S, _
  rw [hS,sum_filter]
  unfold rowCharge
  apply sum_congr rfl
  intro u _
  by_cases hc : comp H.G H.lab F v u = C <;>
    by_cases he : s(v,u) ∈ L <;> simp [hc,he,ind]

lemma sign_sum (S : Finset V) (c : V → Bool) :
    ∑ u ∈ S, sgn (c u) = ((S.filter (fun u => c u = true)).card : ℤ) -
      (S.filter (fun u => c u = false)).card := by
  calc
    _ = (∑ u ∈ S, if c u = true then (1:ℤ) else 0) -
        ∑ u ∈ S, if c u = false then (1:ℤ) else 0 := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro u _
      cases c u <;> norm_num [sgn]
    _ = _ := by simp

theorem rootAdm_of_physical {H : Host V I} {F : Set (Multiset I)}
    (X : SimpleGraph V) [DecidableRel X.Adj] {L : Finset (Sym2 V)}
    (hL : L ⊆ X.edgeFinset) (hphys : IsPhysical H F L) (v : V) :
    rootAdm H.G H.lab F X v (SelSimul.demand X L v) := by
  intro C hC
  let S := SelSimul.demand X L v ∩ (X.neighborFinset v ∩ C)
  have hsum := rowCharge_ind_eq_demand (H := H) (F := F) X hL v hC
  have hrow := physical_row_constraints hphys v C
  change (IsBip H.G H.lab F (v,C) → _ = 0) ∧ _ at hrow
  unfold compAdmC
  by_cases hb : IsBip H.G H.lab F (v,C)
  · rw [if_pos hb]
    have hcol : ∀ u ∈ S, sigma H.G H.lab F (v,C) u = colG H.G H.lab F v u := by
      intro u hu
      have huC := mem_component_iff hC |>.mp (mem_inter.mp (mem_inter.mp hu).2).2
      simp [sigma,hb,colG,huC]
    have hs : (∑ u ∈ S, sgn (colG H.G H.lab F v u)) = 0 := by
      calc
        _ = ∑ u ∈ S, sgn (sigma H.G H.lab F (v,C) u) := by
          apply sum_congr rfl
          intro u hu
          rw [hcol u hu]
        _ = rowCharge H.G H.lab F (ind L) v C := hsum.symm
        _ = 0 := hrow.1 hb
    rw [sign_sum] at hs
    exact_mod_cast (sub_eq_zero.mp hs)
  · rw [if_neg hb]
    have hs : rowCharge H.G H.lab F (ind L) v C = (S.card : ℤ) := by
      rw [hsum]
      simp [sigma,hb,S]
    rw [hs] at hrow
    exact_mod_cast (even_iff_two_dvd.mpr hrow.2)

/-- Fork replacement preserves physicality of the later demand; this uses
the actual lattice difference supplied by `ForkSystem.fork_L`. -/
theorem physical_of_difference {H : Host V I} {F : Set (Multiset I)}
    {L L1 : Finset (Sym2 V)} (hL : IsPhysical H F L)
    (hdiff : ind L - ind L1 ∈ lattice H F) : IsPhysical H F L1 := by
  have heq : ind L1 = ind L - (ind L - ind L1) := by abel
  unfold IsPhysical
  rw [heq]
  exact Submodule.sub_mem _ hL hdiff

theorem fork_L_physical {H : Host V I} {F : Set (Multiset I)}
    {W : Finset V} {X P L : Finset (Sym2 V)} {fk : Sym2 V → S07V26.Fork V}
    (hFS : S07V26.ForkSystem H.G H.lab F W X P fk) (hL : L ⊆ X)
    (hphys : IsPhysical H F L) :
    IsPhysical H F ((L \ (L ∩ S07V26.XZ X W)) ∪ S07V26.QU fk (L ∩ S07V26.XZ X W)) := by
  exact physical_of_difference hphys (hFS.fork_L hL).2.2.2.1

end TypedTriangle.SelectorEntry
