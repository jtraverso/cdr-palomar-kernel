/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SignedGrouping
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TypedTriangle.Grouping
open QuotientBox

/-- Original tokens followed by the two signs of the lattice generators. -/
abbrev AtomLiftIndex (d B : ℕ) (S : Finset (Fin d → ℤ)) :=
  Alph d B ⊕ (S ⊕ S)

def atomLiftColumns (d B : ℕ) (S : Finset (Fin d → ℤ)) :
    AtomLiftIndex d B S → (Fin d → ℤ) :=
  Sum.elim Subtype.val (Sum.elim (fun s => -s.val) Subtype.val)

private def liftMultiplicity {d B : ℕ} (S : Finset (Fin d → ℤ))
    (m : Alph d B → ℕ) (p q : S → ℕ) : AtomLiftIndex d B S → ℕ :=
  Sum.elim m (Sum.elim p q)

private theorem liftMultiplicity_charge {d B : ℕ} (S : Finset (Fin d → ℤ))
    (m : Alph d B → ℕ) (p q : S → ℕ) :
    (∑ i, (liftMultiplicity S m p q i : ℤ) • atomLiftColumns d B S i) =
      charge m - (∑ s : S, (p s : ℤ) • s.val) +
        ∑ s : S, (q s : ℤ) • s.val := by
  simp only [Fintype.sum_sum_type, liftMultiplicity, atomLiftColumns,
    Sum.elim_inl, Sum.elim_inr, smul_neg, sum_neg_distrib, charge]
  abel

/-- A kernel vector retains exact membership in the integer lattice. -/
theorem atomLift_projection_mem_span {d B : ℕ} (S : Finset (Fin d → ℤ))
    (u : AtomLiftIndex d B S → ℕ)
    (hu : (∑ i, (u i : ℤ) • atomLiftColumns d B S i) = 0) :
    charge (fun a => u (Sum.inl a)) ∈ span ℤ (S : Set (Fin d → ℤ)) := by
  let aux : S ⊕ S → Fin d → ℤ := Sum.elim (fun s => -s.val) Subtype.val
  have hAux : (∑ j : S ⊕ S, (u (Sum.inr j) : ℤ) • aux j) ∈
      span ℤ (S : Set (Fin d → ℤ)) := by
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    cases j with
    | inl s => exact Submodule.neg_mem _ (subset_span s.property)
    | inr s => exact subset_span s.property
  have hSplit : charge (fun a => u (Sum.inl a)) +
      (∑ j : S ⊕ S, (u (Sum.inr j) : ℤ) • aux j) = 0 := by
    simpa only [charge, atomLiftColumns, aux, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr] using hu
  rw [eq_neg_of_add_eq_zero_left hSplit]
  exact Submodule.neg_mem _ hAux

private theorem exists_atom_lift {d B : ℕ} (S : Finset (Fin d → ℤ))
    (m : Alph d B → ℕ) (hm : charge m ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ u : AtomLiftIndex d B S → ℕ,
      (∀ a, u (Sum.inl a) = m a) ∧
      (∑ i, (u i : ℤ) • atomLiftColumns d B S i) = 0 := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_finset'.mp hm
  let p : S → ℕ := fun s => (c s).toNat
  let q : S → ℕ := fun s => (-c s).toNat
  have hParts : (∑ s : S, (p s : ℤ) • s.val) -
      (∑ s : S, (q s : ℤ) • s.val) = charge m := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ s : S, ((p s : ℤ) • s.val - (q s : ℤ) • s.val)) =
          ∑ s : S, c s • s.val := by
        apply sum_congr rfl
        intro s _
        rw [← sub_smul]
        have heq : (p s : ℤ) - (q s : ℤ) = c s := by
          dsimp [p,q]
          omega
        rw [heq]
      _ = charge m := hc
  refine ⟨liftMultiplicity S m p q, fun _ => rfl, ?_⟩
  rw [liftMultiplicity_charge, ← hParts]
  abel

private theorem sum_lt_of_le_of_ne {J : Type} [Fintype J]
    {v u : J → ℕ} (hle : v ≤ u) (hne : v ≠ u) :
    (∑ j, v j) < ∑ j, u j := by
  have hex : ∃ j, v j < u j := by
    by_contra h
    push_neg at h
    exact hne (funext fun j => Nat.le_antisymm (hle j) (h j))
  obtain ⟨j,hj⟩ := hex
  exact sum_lt_sum (fun j _ => hle j) ⟨j,mem_univ _,hj⟩

private theorem kernel_charge_sub {J : Type} [Fintype J] {d : ℕ}
    (A : J → Fin d → ℤ) (u v : J → ℕ) (hle : v ≤ u) :
    (∑ j, ((u j - v j : ℕ) : ℤ) • A j) =
      (∑ j, (u j : ℤ) • A j) - ∑ j, (v j : ℤ) • A j := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [Nat.cast_sub (hle j), sub_smul]

/-- Lift a minimal nonzero lattice charge to an irreducible nonnegative
integer kernel vector. The minimum is over actual integer certificates;
neither saturation nor a torsion quotient is used. -/
theorem exists_irreducible_atom_lift {d B : ℕ}
    (S : Finset (Fin d → ℤ)) (m : Alph d B → ℕ)
    (hm : Minimal (IsZeroSum (span ℤ (S : Set (Fin d → ℤ)))) m) :
    ∃ u : AtomLiftIndex d B S → ℕ,
      (∀ a, u (Sum.inl a) = m a) ∧ u ≠ 0 ∧
      (∑ i, (u i : ℤ) • atomLiftColumns d B S i) = 0 ∧
      (∀ v : AtomLiftIndex d B S → ℕ, v ≤ u → v ≠ 0 →
        (∑ i, (v i : ℤ) • atomLiftColumns d B S i) = 0 → v = u) ∧
      (∑ a, m a) ≤ ∑ i, u i := by
  let P : ℕ → Prop := fun n => ∃ u : AtomLiftIndex d B S → ℕ,
    (∀ a, u (Sum.inl a) = m a) ∧
      (∑ i, (u i : ℤ) • atomLiftColumns d B S i) = 0 ∧ ∑ i, u i = n
  have hP : ∃ n, P n := by
    obtain ⟨u,hu,hzero⟩ := exists_atom_lift S m hm.1.2
    exact ⟨∑ i,u i,u,hu,hzero,rfl⟩
  obtain ⟨u,hproj,hzero,hnorm⟩ := Nat.find_spec hP
  have hMinimal : ∀ w : AtomLiftIndex d B S → ℕ,
      (∀ a, w (Sum.inl a) = m a) →
      (∑ i, (w i : ℤ) • atomLiftColumns d B S i) = 0 →
      Nat.find hP ≤ ∑ i,w i := by
    intro w hw hzw
    exact Nat.find_min' hP ⟨w,hw,hzw,rfl⟩
  have hu : u ≠ 0 := by
    intro h
    apply hm.1.1
    funext a
    exact (hproj a).symm.trans (by rw [h]; rfl)
  have hIrreducible : ∀ v : AtomLiftIndex d B S → ℕ,
      v ≤ u → v ≠ 0 →
      (∑ i, (v i : ℤ) • atomLiftColumns d B S i) = 0 → v = u := by
    intro v hv hv0 hzv
    by_cases hFirst : (fun a => v (Sum.inl a)) = 0
    · let w : AtomLiftIndex d B S → ℕ := fun i => u i-v i
      have hwproj : ∀ a, w (Sum.inl a) = m a := by
        intro a
        have hvFirst : v (Sum.inl a) = 0 := by
          simpa only [Pi.zero_apply] using congrFun hFirst a
        simpa only [w,hvFirst,Nat.sub_zero] using hproj a
      have hzw : (∑ i, (w i : ℤ) • atomLiftColumns d B S i) = 0 := by
        rw [show w = (fun i => u i-v i) from rfl,
          kernel_charge_sub _ u v hv,hzero,hzv,sub_self]
      have hwle : w ≤ u := fun i => Nat.sub_le _ _
      have hwne : w ≠ u := by
        intro heq
        apply hv0
        funext i
        have hi : u i - v i = u i := congrFun heq i
        have hcancel := Nat.sub_add_cancel (hv i)
        rw [hi] at hcancel
        change v i = 0
        exact Nat.add_left_cancel (hcancel.trans (Nat.add_zero (u i)).symm)
      have hs := sum_lt_of_le_of_ne hwle hwne
      have hb := hMinimal w hwproj hzw
      omega
    · have hAtom : IsZeroSum (span ℤ (S : Set (Fin d → ℤ)))
          (fun a => v (Sum.inl a)) :=
        ⟨hFirst,atomLift_projection_mem_span S v hzv⟩
      have hle : (fun a => v (Sum.inl a)) ≤ m := by
        intro a
        exact (hv (Sum.inl a)).trans_eq (hproj a)
      have hEqual : (fun a => v (Sum.inl a)) = m :=
        le_antisymm hle (hm.2 hAtom hle)
      by_contra hne
      have hs := sum_lt_of_le_of_ne hv hne
      have hb := hMinimal v (fun a => congrFun hEqual a) hzv
      omega
  refine ⟨u,hproj,hu,hzero,hIrreducible,?_⟩
  rw [Fintype.sum_sum_type]
  have heq : (∑ a, m a) = ∑ a, u (Sum.inl a) := by
    apply sum_congr rfl
    intro a _
    exact (hproj a).symm
  rw [heq]
  exact Nat.le_add_right _ _

theorem atomLift_columns_bounded {d B R : ℕ}
    (S : Finset (Fin d → ℤ)) (hS : S ⊆ box d R) :
    ∀ i k, |atomLiftColumns d B S i k| ≤ (max B R : ℕ) := by
  intro i k
  cases i with
  | inl a =>
    exact (mem_box.mp a.property k).trans (by exact_mod_cast Nat.le_max_left B R)
  | inr s =>
    cases s with
    | inl s =>
      simpa only [atomLiftColumns, Sum.elim_inr, Sum.elim_inl, Pi.neg_apply, abs_neg]
        using (mem_box.mp (hS s.property) k).trans (by exact_mod_cast Nat.le_max_right B R)
    | inr s =>
      exact (mem_box.mp (hS s.property) k).trans (by exact_mod_cast Nat.le_max_right B R)

#print axioms atomLift_projection_mem_span
#print axioms exists_irreducible_atom_lift
#print axioms atomLift_columns_bounded
end TypedTriangle.Grouping
