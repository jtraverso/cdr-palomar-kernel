module
public import RequestProject.TypedTriangle.GroupingScalarZeroSum
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TypedTriangle.GroupingExplicit

/-- An elementary numerical bound, independent of the number of columns.
    The coordinate induction deliberately pays a large bound. -/
def kernelBound : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d + 1, D => (2 * D + 1) * kernelBound d (D * (2 * D + 1))

noncomputable section

theorem kernelBound_pos (d D : ℕ) : 0 < kernelBound d D := by
  induction d generalizing D with
  | zero => simp [kernelBound]
  | succ d ih => exact Nat.mul_pos (by omega) (ih _)

/-- Coordinate induction extracts a bounded nonempty zero-sum subfamily.
    No bound on the cardinality of the input family is assumed. -/
theorem vector_zero_sum_small_block (d : ℕ) :
    ∀ {ι : Type} (D : ℕ) (z : ι → Fin d → ℤ) (s : Finset ι),
      (∀ i ∈ s, ∀ k, |z i k| ≤ (D : ℤ)) → s.Nonempty →
      (∑ i ∈ s, z i = 0) →
      ∃ t ⊆ s, t.Nonempty ∧ t.card ≤ kernelBound d D ∧ ∑ i ∈ t, z i = 0 := by
  induction d with
  | zero =>
    intro ι D z s _ hne _
    obtain ⟨i, hi⟩ := hne
    refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, by simp, by simp [kernelBound], ?_⟩
    funext k
    exact Fin.elim0 k
  | succ d ih =>
    intro ι D z s hz hne hs
    have hscalar : ∑ i ∈ s, z i 0 = 0 := by
      simpa using congrFun hs 0
    obtain ⟨P, hP⟩ := scalar_zero_sum_partition (fun i => z i 0) D s
      (fun i hi => hz i hi 0) hscalar
    let q : Finset ι → Fin d → ℤ := fun b k => ∑ i ∈ b, z i k.succ
    have hparts : P.parts.Nonempty := by
      obtain ⟨i, hi⟩ := hne
      obtain ⟨b, hb, _⟩ := P.exists_mem hi
      exact ⟨b, hb⟩
    have hq : ∀ b ∈ P.parts, ∀ k, |q b k| ≤ (D * (2 * D + 1) : ℕ) := by
      intro b hb k
      calc
        |q b k| ≤ ∑ i ∈ b, |z i k.succ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ b, (D : ℤ) := Finset.sum_le_sum (fun i hi => hz i (P.le hb hi) _)
        _ = (b.card : ℤ) * D := by simp
        _ ≤ (D * (2 * D + 1) : ℕ) := by
          have hc : (b.card : ℤ) ≤ 2 * D + 1 := by exact_mod_cast (hP b hb).1
          push_cast
          nlinarith
    have hq0 : ∑ b ∈ P.parts, q b = 0 := by
      funext k
      simp only [Finset.sum_apply, q, Pi.zero_apply]
      calc
        _ = ∑ i ∈ P.parts.biUnion id, z i k.succ := by
          simpa only [id_eq] using (Finset.sum_biUnion P.disjoint
            (f := fun i => z i k.succ)).symm
        _ = 0 := by rw [P.biUnion_parts]; simpa using congrFun hs k.succ
    obtain ⟨u, huP, hun, huc, hu0⟩ := ih (D * (2 * D + 1)) q P.parts hq hparts hq0
    have hdis : (u : Set (Finset ι)).PairwiseDisjoint id :=
      P.disjoint.subset huP
    refine ⟨u.biUnion id, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨b, hb, hi⟩ := Finset.mem_biUnion.mp hi
      exact P.le (huP hb) hi
    · obtain ⟨b, hb⟩ := hun
      obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts (huP hb)
      exact ⟨i, Finset.mem_biUnion.mpr ⟨b, hb, hi⟩⟩
    · calc
        (u.biUnion id).card ≤ ∑ b ∈ u, b.card := Finset.card_biUnion_le
        _ ≤ ∑ b ∈ u, (2 * D + 1) := Finset.sum_le_sum (fun b hb => (hP b (huP hb)).1)
        _ = u.card * (2 * D + 1) := by simp
        _ ≤ kernelBound d (D * (2 * D + 1)) * (2 * D + 1) := Nat.mul_le_mul_right _ huc
        _ = kernelBound (d + 1) D := by simp only [kernelBound, Nat.mul_comm]
    · funext k
      simp only [Finset.sum_apply, Pi.zero_apply]
      refine Fin.cases ?_ (fun j => ?_) k
      · change (∑ i ∈ u.biUnion id, z i 0) = 0
        rw [Finset.sum_biUnion hdis]
        exact Finset.sum_eq_zero (fun b hb => (hP b (huP hb)).2)
      · change (∑ i ∈ u.biUnion id, z i j.succ) = 0
        rw [Finset.sum_biUnion hdis]
        simpa only [Finset.sum_apply, q, id_eq, Pi.zero_apply] using congrFun hu0 j

#print axioms vector_zero_sum_small_block

end
end TypedTriangle.GroupingExplicit
