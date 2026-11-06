/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalEnvelope
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Uniform constants for the basal envelope: no total-edge budget remains as an
extra input. The handshake bound and a linear centre ceiling pay saturation. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Envelope
open SelSimul
variable {V I : Type*} [Fintype V]

lemma two_card_le_card_mul_degree (E : Finset (Sym2 V)) {r : ℕ}
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hdeg : ∀ v, edeg E v ≤ r) :
    2 * E.card ≤ Fintype.card V * r := by
  have hs := sum_auxCount E (fun e => e.toFinset) (univ : Finset V) (by simp)
  have he : ∑ e ∈ E, e.toFinset.card = 2 * E.card := by
    calc _ = ∑ _e ∈ E, 2 := sum_congr rfl (fun e he => Sym2.card_toFinset_of_not_isDiag e (hdiag e he))
      _ = 2 * E.card := by simp [mul_comm]
  have hv : ∑ v : V, auxCount E (fun e => e.toFinset) v = ∑ v : V, edeg E v := by
    simp only [auxCount,edeg,Sym2.mem_toFinset]
  rw [he,hv] at hs
  calc 2 * E.card = ∑ v : V, edeg E v := hs.symm
    _ ≤ ∑ _v : V, r := sum_le_sum (fun v hv => hdeg v)
    _ = Fintype.card V * r := by simp

/-- The numerical saturation window follows from sparse local budgets.
All constants are fixed before the host or its boundary is chosen. -/
lemma sparse_window {α : ℝ} (hα : 0 < α) {L n r b z m : ℕ}
    (hL : 0 < L) (hαL : 4 ≤ α * L) (hm : 2 * m ≤ n * r)
    (hn : 32 * (L : ℝ) ≤ α * n)
    (hr : (r : ℝ) ≤ α / (64 * ((L : ℝ) + 4)) * n)
    (hb : (b : ℝ) ≤ α / (64 * ((L : ℝ) + 4)) * n)
    (hz : (z : ℝ) ≤ α / (64 * ((L : ℝ) + 4)) * n) :
    ((z + m / (L * (r + 1)) + 2 * (b + 3 * r + 2 * (L * (r + 1))) : ℕ) : ℝ) < α * n := by
  let s := m / (L * (r + 1))
  have hs : 2 * s * L ≤ n := by
    by_cases hr0 : r = 0
    · have hm0 : m = 0 := by rw [hr0] at hm; omega
      simp [s,hm0]
    · have hdiv : s * (L * (r + 1)) ≤ m := Nat.div_mul_le_self _ _
      have hmul : (2 * s * L) * r ≤ n * r := by
        calc _ ≤ (2 * s * L) * (r + 1) := Nat.mul_le_mul_left _ (Nat.le_succ r)
          _ = 2 * (s * (L * (r + 1))) := by ring
          _ ≤ 2 * m := Nat.mul_le_mul_left _ hdiv
          _ ≤ n * r := hm
      exact Nat.le_of_mul_le_mul_right hmul (Nat.pos_of_ne_zero hr0)
  have hsR : 2 * (s : ℝ) * L ≤ n := by exact_mod_cast hs
  have hmass : (s : ℝ) ≤ α * n / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hαL (by positivity : (0 : ℝ) ≤ 2 * s)
    have h2 := mul_le_mul_of_nonneg_left hsR hα.le
    nlinarith
  have hcoef : (9 + 4 * (L : ℝ)) * (α / (64 * ((L : ℝ) + 4))) ≤ α / 8 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show (0 : ℝ) ≤ L by positivity]
  have hcoefN := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hrest : (z : ℝ) + 2 * ((b : ℝ) + 3 * r + 2 * ((L : ℝ) * (r + 1))) ≤ α * n / 4 := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 6 + 4 * L by positivity)
    nlinarith
  have hn0 : 0 < α * n := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 32) (by exact_mod_cast hL)) hn
  have htotal : (z : ℝ) + s + 2 * ((b : ℝ) + 3 * r + 2 * ((L : ℝ) * (r + 1))) < α * n := by
    nlinarith
  simpa only [s,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using htotal

end TypedTriangle.Envelope

namespace TypedTriangle.Envelope
open SelSimul

/-- Every sufficiently sparse boundary with permitted thirds has a basal envelope
with uniformly linear maximum degree. Constants precede the host and the boundary.
This is a construction theorem from H3, not a supplied envelope provider. -/
theorem uniform_envelope_of_H3 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℕ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α →
        ∀ (E B : Finset (Sym2 V)) (Z : Finset V) (r b : ℕ),
          (∀ v, edeg E v ≤ r) → (∀ v, edeg B v ≤ b) →
          (r : ℝ) ≤ ε * Fintype.card V → (b : ℝ) ≤ ε * Fintype.card V →
          (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ e ∈ E, HasTri H F e) →
          ∃ W : Finset (Sym2 V), Disjoint W (E ∪ B) ∧ Basal H F (E ∪ W) ∧
            ∀ v, edeg W v ≤ C * (r + 1) := by
  let L : ℕ := ⌈4 / α⌉₊ + 1
  let ε : ℝ := α / (64 * ((L : ℝ) + 4))
  have hL : 0 < L := by dsimp [L]; omega
  have hαL : 4 ≤ α * L := by
    have hc : 4 / α ≤ (L : ℝ) := (Nat.le_ceil _).trans (by dsimp [L]; push_cast; linarith)
    have hd := (div_le_iff₀ hα).mp hc
    nlinarith
  refine ⟨2 + 2 * L,by positivity,ε,by dsimp [ε]; positivity,⌈32 * (L : ℝ) / α⌉₊ + 1,?_⟩
  intro V I _ H F hn hH3 E B Z r b hE hB hr hb hz htri
  classical
  have hnR : 32 * (L : ℝ) / α ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈32 * (L : ℝ) / α⌉₊ ≤ Fintype.card V by omega))
  have hn' : 32 * (L : ℝ) ≤ α * Fintype.card V := by
    have hh := (div_le_iff₀ hα).mp hnR
    nlinarith
  have hdiag : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    obtain ⟨T,hT,heT⟩ := htri e he
    exact (mem_filter.mp heT).2
  have hm := two_card_le_card_mul_degree E hdiag hE
  have hwin := sparse_window hα hL hαL hm hn' hr hb hz
  obtain ⟨W,hW,hbas,hWd⟩ := envelope_of_H3 hH3 E B Z
    (Nat.mul_pos hL (Nat.succ_pos r)) hE hB htri hwin
  refine ⟨W,hW,hbas,fun v => (hWd v).trans ?_⟩
  calc 2 * (r + L * (r + 1)) ≤ 2 * ((r + 1) + L * (r + 1)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_succ r) _)
    _ = (2 + 2 * L) * (r + 1) := by ring

/-- Uniform envelope directly from original H2--H3; no third-triangle provider. -/
theorem uniform_envelope_of_H2H3 (α : ℝ) (hα : 0 < α) :
    ∃ C : ℕ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → IsPhysical H F (edges H) → CommonNbrCond H F α →
        ∀ (E B : Finset (Sym2 V)) (Z : Finset V) (r b : ℕ),
          E ⊆ edges H → (∀ v, edeg E v ≤ r) → (∀ v, edeg B v ≤ b) →
          (r : ℝ) ≤ ε * Fintype.card V → (b : ℝ) ≤ ε * Fintype.card V →
          (Z.card : ℝ) ≤ ε * Fintype.card V →
          ∃ W : Finset (Sym2 V), Disjoint W (E ∪ B) ∧ Basal H F (E ∪ W) ∧
            ∀ v, edeg W v ≤ C * (r + 1) := by
  obtain ⟨C,hC,ε,hε,n₀,hmain⟩ := uniform_envelope_of_H3 α hα
  refine ⟨C,hC,ε,hε,n₀,?_⟩
  intro V I _ H F hn hH2 hH3 E B Z r b hEH hE hB hr hb hz
  exact hmain H F hn hH3 E B Z r b hE hB hr hb hz
    (fun e he => hasTri_of_physical_host hH2 (hEH he))

end TypedTriangle.Envelope
