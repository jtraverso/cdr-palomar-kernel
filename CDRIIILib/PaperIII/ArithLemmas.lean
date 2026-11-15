/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.Arith

/-!
# Real-variable lemmas for `split_near`
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

/-- `|M - m v²| ≤ (20 + 4k) v`. -/
theorem M_estimate {v k W PF Sq QF m E G H SQ w M : ℝ} (hk : 0 ≤ k) (hv : 0 ≤ v)
    (hW : W + PF = 1) (hSq : Sq + QF = 1 / 3) (hm : m = 4 * Sq - W ^ 2)
    (hw : w = W * v - E) (hSQ : SQ = QF * v ^ 2 + 2 * v * G + H)
    (hM : M = 4 * ((v ^ 2 + 2 * v) / 3 - SQ) - w ^ 2)
    (hE1 : -(2 * k) ≤ E) (hE2 : E ≤ 0) (hG1 : -2 ≤ G) (hG2 : G ≤ 0) (hH1 : 0 ≤ H)
    (hH2 : H ≤ 4 * k) (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (hvbig : 16 * k + 4 * k ^ 2 ≤ v) :
    |M - m * v ^ 2| ≤ (20 + 4 * k) * v := by
  have key : M - m * v ^ 2 = 8 * v / 3 - 8 * v * G - 4 * H + 2 * W * v * E - E ^ 2 := by
    rw [hM, hSQ, hw, hm]
    have hQF : QF = 1 / 3 - Sq := by linarith
    rw [hQF]; ring
  have hWE : -(2 * k) ≤ W * E := by nlinarith
  have hWE2 : W * E ≤ 0 := by nlinarith
  have hvWE1 : -(2 * k) * v ≤ W * v * E := by nlinarith
  have hvWE2 : W * v * E ≤ 0 := by nlinarith
  have hvG1 : -2 * v ≤ v * G := by nlinarith
  have hvG2 : v * G ≤ 0 := by nlinarith
  have hE2' : E ^ 2 ≤ 4 * k ^ 2 := by nlinarith
  have hE20 : 0 ≤ E ^ 2 := sq_nonneg E
  have hkv : 0 ≤ k * v := mul_nonneg hk hv
  rw [key, abs_le]
  constructor <;> nlinarith

/-- Deviation of a coordinate of the representation from `v · uu`. -/
theorem dev_bound {y sN sm v m ε K1 uu : ℝ} (hsm : 0 < sm) (hm : 0 < m)
    (hy : |y - sN * (uu / sm)| ≤ ε * sN) (hu : |uu| ≤ (1 + m) / 2)
    (hratio : |sN / sm - v| ≤ K1 / m) (hK1 : 0 ≤ K1) :
    |y - v * uu| ≤ ε * sN + (1 + m) * K1 / (2 * m) := by
  have e : y - v * uu = (y - sN * (uu / sm)) + uu * (sN / sm - v) := by field_simp; ring
  rw [e]
  calc |(y - sN * (uu / sm)) + uu * (sN / sm - v)|
      ≤ |y - sN * (uu / sm)| + |uu| * |sN / sm - v| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ε * sN + (1 + m) / 2 * (K1 / m) := by
        have : |uu| * |sN / sm - v| ≤ (1 + m) / 2 * (K1 / m) :=
          mul_le_mul hu hratio (abs_nonneg _) (by positivity)
        linarith
    _ = ε * sN + (1 + m) * K1 / (2 * m) := by ring

/-- The four classes are close to their targets. -/
theorem four_close {c0 c1 c2 c3 q0 q1 q2 q3 w W v E y0 y1 y2 u0 u2 D k : ℝ}
    (e0 : 4 * c0 = w + (y0 + y1 + y2)) (e1 : 4 * c1 = w + (y0 - y1 - y2))
    (e2 : 4 * c2 = w + (-y0 + y1 - y2)) (e3 : 4 * c3 = w + (-y0 - y1 + y2))
    (hW : W = q0 + q1 + q2 + q3) (hsym : q1 = q0 + q2 - q3)
    (hu0 : u0 = 2 * (q0 - q3)) (hu2 : u2 = 2 * (q3 - q2))
    (hw : w = W * v - E) (hE : |E| ≤ 2 * k)
    (d0 : |y0 - v * u0| ≤ D) (d1 : |y1| ≤ D) (d2 : |y2 - v * u2| ≤ D) :
    |c0 - q0 * v| ≤ (2 * k + 3 * D) / 4 ∧ |c1 - q1 * v| ≤ (2 * k + 3 * D) / 4 ∧
      |c2 - q2 * v| ≤ (2 * k + 3 * D) / 4 ∧ |c3 - q3 * v| ≤ (2 * k + 3 * D) / 4 := by
  obtain ⟨a0, b0⟩ := abs_le.1 d0
  obtain ⟨a1, b1⟩ := abs_le.1 d1
  obtain ⟨a2, b2⟩ := abs_le.1 d2
  obtain ⟨aE, bE⟩ := abs_le.1 hE
  subst hW hsym hu0 hu2 hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith

end CDRBicolour.PaperIII
