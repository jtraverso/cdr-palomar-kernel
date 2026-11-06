module
public import RequestProject.TypedTriangle.QuotientBox
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Submodule Module Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TypedTriangle.QuotientBox

def explicitTorsionRadius (d R : ℕ) : ℕ := R * (2 * R + 1) ^ d
def explicitTorsionBound (d R : ℕ) : ℕ := (2 * explicitTorsionRadius d R + 1) ^ d

noncomputable section

theorem card_box (d R : ℕ) : (box d R).card = (2 * R + 1) ^ d := by
  have hI : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  simp [box, Fintype.card_piFinset, hI]

/-- Dividing the coefficients of an integer lattice certificate gives a
    bounded representative. No basis, saturation, or torsion is discarded. -/
theorem exists_bounded_lattice_representative (d R : ℕ)
    (S : Finset (Fin d → ℤ)) (hS : ∀ s ∈ S, ∀ k, |s k| ≤ (R : ℤ))
    (x : Fin d → ℤ) (n : ℤ) (hn : n ≠ 0)
    (hx : n • x ∈ span ℤ (S : Set (Fin d → ℤ))) :
    ∃ y : Fin d → ℤ, (∀ k, |y k| ≤ (S.card * R : ℕ)) ∧
      x - y ∈ span ℤ (S : Set (Fin d → ℤ)) := by
  let N : ℤ := |n|
  have hN : 0 < N := abs_pos.mpr hn
  have hNx : N • x ∈ span ℤ (S : Set (Fin d → ℤ)) := by
    rcases le_total 0 n with hn0 | hn0
    · simpa only [N, abs_of_nonneg hn0] using hx
    · simpa only [N, abs_of_nonpos hn0, neg_smul] using
        (span ℤ (S : Set (Fin d → ℤ))).neg_mem hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hNx
  let q : S → ℤ := fun s => c s / N
  let r : S → ℤ := fun s => c s % N
  let m : Fin d → ℤ := ∑ s : S, q s • s.val
  let y := x - m
  refine ⟨y, ?_, ?_⟩
  · intro k
    have hcZ : N * x k = ∑ s : S, c s * s.val k := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (congrFun hc k).symm
    have hy : N * y k = ∑ s : S, r s * s.val k := by
      have hmcoord : m k = ∑ s : S, q s * s.val k := by
        simp only [m, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change N * (x k - m k) = _
      rw [hmcoord]
      rw [mul_sub, hcZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      have he : c s - N * q s = r s := by
        change c s - N * (c s / N) = c s % N
        linear_combination -(Int.emod_add_mul_ediv (c s) N)
      calc
        c s * s.val k - N * (q s * s.val k) = (c s - N * q s) * s.val k := by ring
        _ = r s * s.val k := by rw [he]
    have hbound : N * |y k| ≤ N * ((S.card : ℤ) * R) := by
      calc
        N * |y k| = |N * y k| := by rw [abs_mul, abs_of_nonneg hN.le]
        _ = |∑ s : S, r s * s.val k| := by rw [hy]
        _ ≤ ∑ s : S, |r s * s.val k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _s : S, N * (R : ℤ) := by
          apply Finset.sum_le_sum
          intro s _
          have hr0 : 0 ≤ r s := Int.emod_nonneg _ (ne_of_gt hN)
          have hrN : r s ≤ N := (Int.emod_lt_of_pos _ hN).le
          rw [abs_mul, abs_of_nonneg hr0]
          exact mul_le_mul hrN (hS s.val s.property k) (abs_nonneg _) hN.le
        _ = N * ((S.card : ℤ) * R) := by simp; ring
    have hfinal : |y k| ≤ (S.card : ℤ) * R := le_of_mul_le_mul_left hbound hN
    exact_mod_cast hfinal
  · have hm : m ∈ span ℤ (S : Set (Fin d → ℤ)) := by
      apply Submodule.sum_mem
      intro s _
      exact Submodule.smul_mem _ _ (Submodule.subset_span s.property)
    simpa only [y, sub_sub_cancel] using hm

theorem torCard_le_explicit (d R : ℕ) (S : Finset (Fin d → ℤ))
    (hS : S ⊆ box d R) :
    torCard d (span ℤ (S : Set (Fin d → ℤ))) ≤ explicitTorsionBound d R := by
  let Γ := span ℤ (S : Set (Fin d → ℤ))
  have hc : S.card ≤ (2 * R + 1) ^ d := by
    simpa only [card_box] using Finset.card_le_card hS
  have hrep : ∀ t : torsion ℤ ((Fin d → ℤ) ⧸ Γ),
      ∃ y : ↥(box d (explicitTorsionRadius d R)), Γ.mkQ y.val = t.val := by
    intro t
    obtain ⟨n, hn⟩ := t.property
    obtain ⟨x, hx⟩ := Γ.mkQ_surjective t.val
    have hn0 : (n : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp n.property
    have hnx : (n : ℤ) • x ∈ Γ := by
      apply (Submodule.Quotient.mk_eq_zero Γ).mp
      change Γ.mkQ ((n : ℤ) • x) = 0
      rw [map_smul, hx]
      exact hn
    obtain ⟨y, hy, hxy⟩ := exists_bounded_lattice_representative d R S
      (fun s hs => mem_box.mp (hS hs)) x n hn0 hnx
    have hybox : y ∈ box d (explicitTorsionRadius d R) := by
      apply mem_box.mpr
      intro k
      have hRad : S.card * R ≤ explicitTorsionRadius d R := by
        simpa only [explicitTorsionRadius, Nat.mul_comm] using Nat.mul_le_mul_right R hc
      exact (hy k).trans (by exact_mod_cast hRad)
    refine ⟨⟨y, hybox⟩, ?_⟩
    have hmk : Γ.mkQ (x - y) = 0 := (Submodule.Quotient.mk_eq_zero Γ).mpr hxy
    rw [map_sub, hx, sub_eq_zero] at hmk
    exact hmk.symm
  let f : torsion ℤ ((Fin d → ℤ) ⧸ Γ) → ↥(box d (explicitTorsionRadius d R)) :=
    fun t => Classical.choose (hrep t)
  have hf : Function.Injective f := by
    intro t u h
    apply Subtype.ext
    calc
      t.val = Γ.mkQ (f t).val := (Classical.choose_spec (hrep t)).symm
      _ = Γ.mkQ (f u).val := by rw [h]
      _ = u.val := Classical.choose_spec (hrep u)
  have hcard := Nat.card_le_card_of_injective f hf
  have htarget : Nat.card ↥(box d (explicitTorsionRadius d R)) =
      explicitTorsionBound d R := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_box]
    rfl
  rw [htarget] at hcard
  exact hcard

theorem torBound_le_explicit (d R : ℕ) : torBound d R ≤ explicitTorsionBound d R := by
  unfold torBound
  apply Finset.sup_le
  intro S hS
  exact torCard_le_explicit d R S (Finset.mem_powerset.mp hS)

#print axioms exists_bounded_lattice_representative
#print axioms torBound_le_explicit

end
end TypedTriangle.QuotientBox
