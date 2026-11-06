/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V34.Uniform
public import RequestProject.S07V33.Recurrence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Bounded coordinate box, V33 recurrence adapter, edge cases (V34, part 4)

* `box d R`: the integer coordinate box `{v ∈ ℤ^d | ∀ i, |v i| ≤ R}` as a `Finset`.
* `uniform_monitor_payment_box`: the main theorem with `B = box d R`; hypotheses are plain
  coordinate bounds on the vectors of `S, C, D`. `A, M` depend only on `d, R`.
* `uniform_step_payment`: the one-step form of the V33 recurrence. If the defect is
  `x = y₀ + ∑_{b ∈ B} n_b • b` with `‖ψ(y₀)‖₁ ≤ E` and `∑ |n_b| ≤ S'` (earlier payments, made by
  generators of any stratum in `B`, evaluated by the SAME monitor), then the word has natural
  cost `∑ |z_c| ≤ A * (1 + E + M * S')`.
* `uniform_cumulative_bound`: the same constants `A, M` feed `S07V33.cumulative_bound`.
* Edge cases: `empty_configuration`, `rank_zero_configuration`, and a nontrivial torsion
  quotient `torsion_quotient_nontrivial` (`ℤ ⧸ 2ℤ`) covered by the theorem.
-/

namespace S07V34

open Finset S07V32

/-- The integer coordinate box of radius `R` in `ℤ^d`. -/
def box (d R : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

lemma mem_box {d R : ℕ} {v : Fin d → ℤ} : v ∈ box d R ↔ ∀ i, |v i| ≤ R := by
  simp [box, Fintype.mem_piFinset, abs_le]

lemma subset_box {d R : ℕ} {S : Finset (Fin d → ℤ)} (h : ∀ v ∈ S, ∀ i, |v i| ≤ R) :
    S ⊆ box d R := fun v hv => mem_box.mpr (h v hv)

/-- **Bounded-coordinate-box specialization.** `A, M` depend only on `d` and `R`. -/
theorem uniform_monitor_payment_box (d R : ℕ) :
    ∃ A M : ℕ, ∀ S D : Finset (Fin d → ℤ),
      (∀ v ∈ S, ∀ i, |v i| ≤ R) → (∀ v ∈ D, ∀ i, |v i| ≤ R) →
      ∃ (k : ℕ) (psi : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ)),
        (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b : Fin d → ℤ, (∀ i, |b i| ≤ R) →
          l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
        ∀ C : Finset (Fin d → ℤ), (∀ v ∈ C, ∀ i, |v i| ≤ R) → ∀ x ∈ Kgrp S C, ∃ z : C → ℤ,
          x + ∑ c : C, z c • qmk S (c : Fin d → ℤ) ∈ Hgrp S D ∧
            ∑ c : C, |z c| ≤ (A : ℤ) * (1 + l1 (psi (x : Qt S ⧸ Hgrp S D))) := by
  obtain ⟨A, M, h⟩ := uniform_monitor_payment d (box d R)
  refine ⟨A, M, fun S D hS hD => ?_⟩
  obtain ⟨k, psi, hk, hM, hpay⟩ := h S D (subset_box hS) (subset_box hD)
  exact ⟨k, psi, hk, fun b hb => hM b (mem_box.mpr hb), fun C hC => hpay C (subset_box hC)⟩

/-- **Adapter to the V33 one-step recurrence.** Same uniform constants; natural costs. -/
theorem uniform_step_payment (d : ℕ) (B : Finset (Fin d → ℤ)) :
    ∃ A M : ℕ, ∀ S D : Finset (Fin d → ℤ), S ⊆ B → D ⊆ B →
      ∃ (k : ℕ) (psi : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ)),
        (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b ∈ B, l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
        ∀ C : Finset (Fin d → ℤ), C ⊆ B → ∀ (E S' : ℕ) (y0 : Qt S) (n : (Fin d → ℤ) → ℤ),
          y0 + ∑ b ∈ B, n b • qmk S b ∈ Kgrp S C →
          l1 (psi (y0 : Qt S ⧸ Hgrp S D)) ≤ E → ∑ b ∈ B, |n b| ≤ S' →
          ∃ z : C → ℤ,
            (y0 + ∑ b ∈ B, n b • qmk S b) + ∑ c : C, z c • qmk S (c : Fin d → ℤ) ∈ Hgrp S D ∧
              ∑ c : C, (z c).natAbs ≤ A * (1 + E + M * S') := by
  obtain ⟨A, M, h⟩ := uniform_monitor_payment d B
  refine ⟨A, M, fun S D hS hD => ?_⟩
  obtain ⟨k, psi, hk, hM, hpay⟩ := h S D hS hD
  refine ⟨k, psi, hk, hM, fun C hC E S' y0 n hx hE hS' => ?_⟩
  obtain ⟨z, hz, hb⟩ := hpay C hC _ hx
  refine ⟨z, hz, ?_⟩
  have hmon : l1 (psi ((y0 + ∑ b ∈ B, n b • qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤
      (E : ℤ) + M * S' := by
    have hsplit : ((y0 + ∑ b ∈ B, n b • qmk S b : Qt S) : Qt S ⧸ Hgrp S D) =
        (y0 : Qt S ⧸ Hgrp S D) + ∑ b ∈ B, n b • ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D) := by
      simp [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sum, QuotientAddGroup.mk_zsmul]
    rw [hsplit, map_add]
    have h1 := l1_add_le (psi (y0 : Qt S ⧸ Hgrp S D))
      (psi (∑ b ∈ B, n b • ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)))
    have h2 := l1_map_sum_le (G := Qt S ⧸ Hgrp S D) psi B
      (fun b => ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) n M
    replace h2 := h2 hM
    have h3 : (M : ℤ) * ∑ b ∈ B, |n b| ≤ M * S' :=
      mul_le_mul_of_nonneg_left hS' (by positivity)
    linarith
  have hcast : ((∑ c : C, (z c).natAbs : ℕ) : ℤ) = ∑ c : C, |z c| := by
    rw [Nat.cast_sum]; exact sum_congr rfl fun c _ => Int.natCast_natAbs _
  have : ((∑ c : C, (z c).natAbs : ℕ) : ℤ) ≤ ((A * (1 + E + M * S') : ℕ) : ℤ) := by
    rw [hcast]
    refine hb.trans ?_
    push_cast
    have hA0 : (0 : ℤ) ≤ A := by positivity
    nlinarith
  exact_mod_cast this

/-- **Uniform constants feed the V33 cumulative recurrence.** The constants `A, M` from
`uniform_step_payment` are fixed (from `d, B`) before the number of stages `P` and the
sequences `N, E`; any stage costs obeying the one-step bound obey the V33 cumulative bound. -/
theorem uniform_cumulative_bound (d : ℕ) (B : Finset (Fin d → ℤ)) :
    ∃ A M : ℕ,
      (∀ S D : Finset (Fin d → ℤ), S ⊆ B → D ⊆ B →
        ∃ (k : ℕ) (psi : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ)),
          (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
          (∀ b ∈ B, l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
          ∀ C : Finset (Fin d → ℤ), C ⊆ B → ∀ (E S' : ℕ) (y0 : Qt S) (n : (Fin d → ℤ) → ℤ),
            y0 + ∑ b ∈ B, n b • qmk S b ∈ Kgrp S C →
            l1 (psi (y0 : Qt S ⧸ Hgrp S D)) ≤ E → ∑ b ∈ B, |n b| ≤ S' →
            ∃ z : C → ℤ,
              (y0 + ∑ b ∈ B, n b • qmk S b) + ∑ c : C, z c • qmk S (c : Fin d → ℤ) ∈ Hgrp S D ∧
                ∑ c : C, (z c).natAbs ≤ A * (1 + E + M * S')) ∧
      ∀ (P : ℕ) (N E : ℕ → ℕ), MonotoneOn E (Set.Iio P) →
        (∀ s < P, N s ≤ A * (1 + E s + M * ∑ i ∈ range s, N i)) →
        ∀ s < P, ∑ i ∈ range (s + 1), N i ≤ A * P * (1 + A * M) ^ P * (1 + E s) := by
  obtain ⟨A, M, h⟩ := uniform_step_payment d B
  exact ⟨A, M, h, fun P N E hE hrec => S07V33.cumulative_bound A M P N E hE hrec⟩

/-! ## Edge cases covered by the uniform theorem -/

/-- Empty configuration `S = C = D = ∅` (here `Q = ℤ^d`, `K = H = 0`). -/
theorem empty_configuration (d : ℕ) (B : Finset (Fin d → ℤ)) :
    ∃ A M : ℕ, ∃ (k : ℕ) (psi : Qt (∅ : Finset (Fin d → ℤ)) ⧸ Hgrp ∅ ∅ →+ (Fin k → ℤ)),
      (psi.ker : Set (Qt (∅ : Finset (Fin d → ℤ)) ⧸ Hgrp ∅ ∅)).Finite ∧
      (∀ b ∈ B, l1 (psi ((qmk ∅ b : Qt ∅) : Qt ∅ ⧸ Hgrp ∅ ∅)) ≤ M) ∧
      ∀ x ∈ Kgrp (∅ : Finset (Fin d → ℤ)) ∅, ∃ z : (∅ : Finset (Fin d → ℤ)) → ℤ,
        x + ∑ c : (∅ : Finset (Fin d → ℤ)), z c • qmk ∅ (c : Fin d → ℤ) ∈ Hgrp ∅ ∅ ∧
          ∑ c : (∅ : Finset (Fin d → ℤ)), |z c| ≤ (A : ℤ) * (1 + l1 (psi (x : Qt ∅ ⧸ Hgrp ∅ ∅))) := by
  obtain ⟨A, M, h⟩ := uniform_monitor_payment d B
  obtain ⟨k, psi, hk, hM, hpay⟩ := h ∅ ∅ (empty_subset _) (empty_subset _)
  exact ⟨A, M, k, psi, hk, hM, hpay ∅ (empty_subset _)⟩

/-- Free rank zero: `d = 0` (`Q` trivial). -/
theorem rank_zero_configuration (B : Finset (Fin 0 → ℤ)) :
    ∃ A M : ℕ, ∀ S D : Finset (Fin 0 → ℤ), S ⊆ B → D ⊆ B →
      ∃ (k : ℕ) (psi : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ)),
        (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b ∈ B, l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
        ∀ C : Finset (Fin 0 → ℤ), C ⊆ B → ∀ x ∈ Kgrp S C, ∃ z : C → ℤ,
          x + ∑ c : C, z c • qmk S (c : Fin 0 → ℤ) ∈ Hgrp S D ∧
            ∑ c : C, |z c| ≤ (A : ℤ) * (1 + l1 (psi (x : Qt S ⧸ Hgrp S D))) :=
  uniform_monitor_payment 0 B

/-- The vector `(2) ∈ ℤ^1`. -/
def vtwo : Fin 1 → ℤ := fun _ => 2
/-- The vector `(1) ∈ ℤ^1`. -/
def vone : Fin 1 → ℤ := fun _ => 1

/-- Nontrivial torsion: in `Q = ℤ^1 ⧸ ⟨(2)⟩` the class of `(1)` is nonzero and `2 • (1) = 0`.
The uniform theorem for `B = {(1), (2)}` covers `S = {(2)}`, so its monitor must handle this
torsion through its finite kernel. -/
theorem torsion_quotient_nontrivial :
    qmk {vtwo} vone ≠ 0 ∧ (2 : ℤ) • qmk {vtwo} vone = 0 := by
  constructor
  · intro h
    have hmem : vone ∈ AddSubgroup.closure ((({vtwo} : Finset (Fin 1 → ℤ))) : Set (Fin 1 → ℤ)) :=
      (QuotientAddGroup.eq_zero_iff _).mp h
    rw [Finset.coe_singleton, ← AddSubgroup.zmultiples_eq_closure] at hmem
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have := congrFun hn 0
    simp [vone, vtwo] at this
    omega
  · have : (2 : ℤ) • qmk {vtwo} vone = qmk {vtwo} vtwo := by
      unfold qmk
      rw [← QuotientAddGroup.mk_zsmul]
      congr 1
    rw [this]
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      (AddSubgroup.subset_closure (by simp))

/-- Torsion instance of the uniform theorem: `B = {(1), (2)}` in `ℤ^1`. -/
theorem torsion_configuration :
    ∃ A M : ℕ, ∀ S D : Finset (Fin 1 → ℤ), S ⊆ {vone, vtwo} → D ⊆ {vone, vtwo} →
      ∃ (k : ℕ) (psi : Qt S ⧸ Hgrp S D →+ (Fin k → ℤ)),
        (psi.ker : Set (Qt S ⧸ Hgrp S D)).Finite ∧
        (∀ b ∈ ({vone, vtwo} : Finset (Fin 1 → ℤ)),
          l1 (psi ((qmk S b : Qt S) : Qt S ⧸ Hgrp S D)) ≤ M) ∧
        ∀ C : Finset (Fin 1 → ℤ), C ⊆ {vone, vtwo} → ∀ x ∈ Kgrp S C, ∃ z : C → ℤ,
          x + ∑ c : C, z c • qmk S (c : Fin 1 → ℤ) ∈ Hgrp S D ∧
            ∑ c : C, |z c| ≤ (A : ℤ) * (1 + l1 (psi (x : Qt S ⧸ Hgrp S D))) :=
  uniform_monitor_payment 1 {vone, vtwo}

end S07V34
