/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ChargePolarization
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ChargePolar
variable {V I : Type*} [Fintype V]

def signedWord : List (Bool × Sym2 V) → (Sym2 V → ℤ)
  | [] => 0
  | z :: l => (if z.1 then ind {z.2} else -ind {z.2}) + signedWord l

/-- Signed repetitions are replaced by pairwise disjoint positive edges.
The resource bound depends on the word length, not on an initial certificate. -/
theorem word_polarization {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (h3 : CommonNbrCond H F α) (l : List (Bool × Sym2 V)) (U : Finset V)
    (B : Finset (Sym2 V)) {b : ℕ} (hB : ∀ v, SelSimul.edeg B v ≤ b)
    (hTri : ∀ z ∈ l, HasTri H F z.2)
    (hRoots : ∀ z ∈ l, ∀ v ∈ z.2, v ∈ U)
    (hwin : ((U.card+3*l.length+2*b+2:ℕ):ℝ) < α*Fintype.card V) :
    ∃ (A : Finset V) (Y : Finset (Sym2 V)), A.card ≤ 3*l.length ∧
      Disjoint A U ∧ Y.card ≤ 4*l.length ∧ Disjoint Y B ∧ Fresh U Y ∧
      Inside (U ∪ A) Y ∧ Y ⊆ edges H ∧ ind Y-signedWord l ∈ lattice H F := by
  induction l with
  | nil =>
    refine ⟨∅,∅,by simp,by simp,by simp,by simp,?_,?_,by simp,?_⟩
    · intro e he; simp at he
    · intro e he; simp at he
    · simp only [signedWord,ind_empty,sub_zero]
      exact Submodule.zero_mem _
  | cons z l ih =>
    have hTri' : ∀ w ∈ l, HasTri H F w.2 := fun w hw => hTri w (List.mem_cons_of_mem _ hw)
    have hRoots' : ∀ w ∈ l, ∀ v ∈ w.2, v ∈ U := fun w hw => hRoots w (List.mem_cons_of_mem _ hw)
    have hwin' : ((U.card+3*l.length+2*b+2:ℕ):ℝ) < α*Fintype.card V := by
      have hle : U.card+3*l.length+2*b+2 ≤ U.card+3*(z::l).length+2*b+2 := by simp
      exact (show ((U.card+3*l.length+2*b+2:ℕ):ℝ) ≤ (U.card+3*(z::l).length+2*b+2:ℕ) by exact_mod_cast hle).trans_lt hwin
    obtain ⟨A0,Y0,hA0,hA0U,hY0,hY0B,hF0,hI0,hE0,hL0⟩ := ih hTri' hRoots' hwin'
    have hcard : (U ∪ A0).card+2*b+2 ≤ U.card+3*(z::l).length+2*b+2 := by
      have := card_union_le U A0
      simp only [List.length_cons]
      omega
    have hw1 : (((U ∪ A0).card+2*b+2:ℕ):ℝ) < α*Fintype.card V :=
      (show (((U ∪ A0).card+2*b+2:ℕ):ℝ) ≤ (U.card+3*(z::l).length+2*b+2:ℕ) by exact_mod_cast hcard).trans_lt hwin
    obtain ⟨A1,Y1,hA1,hA1U,hY1,hY1B,hF1,hI1,hE1,hL1⟩ :=
      edge_polarization h3 (hTri z (by simp)) z.1 (U ∪ A0)
        (fun v hv => mem_union_left _ (hRoots z (by simp) v hv)) B hB hw1
    have hdis : Disjoint Y0 Y1 := hI0.disjoint_fresh hF1
    refine ⟨A0 ∪ A1,Y0 ∪ Y1,?_,?_,?_,disjoint_union_left.mpr ⟨hY0B,hY1B⟩,
      hF0.union (hF1.anti (subset_union_left)),?_,union_subset hE0 hE1,?_⟩
    · have := card_union_le A0 A1
      simp only [List.length_cons]
      omega
    · apply disjoint_union_left.mpr
      exact ⟨hA0U,hA1U.mono_right subset_union_left⟩
    · have := card_union_le Y0 Y1
      simp only [List.length_cons]
      omega
    · apply Inside.union
      · apply hI0.mono
        intro v hv
        rcases mem_union.mp hv with hv | hv
        · exact mem_union_left _ hv
        · exact mem_union_right _ (mem_union_left _ hv)
      · exact hI1.mono (by intro v hv; simpa only [union_assoc] using hv)
    · have hsum := Submodule.add_mem (lattice H F) hL0 hL1
      have heq : ind (Y0 ∪ Y1)-signedWord (z::l) =
          (ind Y0-signedWord l)+(ind Y1-(if z.1 then ind {z.2} else -ind {z.2})) := by
        rw [ind_union_of_disjoint hdis,signedWord]
        abel
      rwa [heq]

end TypedTriangle.ChargePolar
