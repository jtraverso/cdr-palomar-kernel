/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.ExplicitAsymptotics
public import RequestProject.Pseudorandom.ExplicitNibbleCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section
namespace Pseudorandom.Nibble
open Pseudorandom.Explicit Finset

def nibbleCut (r : ℕ) (ρ κ σ : ℝ) : ℝ :=
  let C := 24*(r:ℝ)^2*Real.exp r
  let γ := 1-(2*r+4)*ρ-κ
  max 2 (max (powerCut (2*ρ) (4*r))
    (max (powerCut (1-κ-2*r*ρ) (4*r^2*Real.exp r))
    (max (powerCut (1-2*(r-1)*ρ) (Real.exp r))
    (max (powerCut ρ (r+5))
    (max (powerCut γ (4*C*Real.log r))
    (max (logCut γ (4*C*(3+2*ρ)))
    (max (powerCut (γ-σ) (2*C)) (logCut (1-2*ρ) (4*ρ)))))))))

theorem nibbleFacts_explicit (r : ℕ) (hr : 1 ≤ r) {ρ κ σ D : ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hsum : (2*r+4)*ρ+κ+σ < 1) (hD : nibbleCut r ρ κ σ ≤ D) :
    NibbleFacts r ρ κ σ D := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  let C : ℝ := 24*(r:ℝ)^2*Real.exp r
  let γ : ℝ := 1-(2*r+4)*ρ-κ
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hγσ : σ < γ := by dsimp [γ]; linarith
  have hγ0 : 0 < γ := by linarith
  have e4 : 0 < 1-κ-2*r*ρ := by nlinarith
  have e5 : 0 < 1-2*(r-1)*ρ := by nlinarith
  have e8 : 0 < 1-2*ρ := by nlinarith
  have bounds : 2 ≤ D ∧ powerCut (2*ρ) (4*r) ≤ D ∧
      powerCut (1-κ-2*r*ρ) (4*r^2*Real.exp r) ≤ D ∧
      powerCut (1-2*(r-1)*ρ) (Real.exp r) ≤ D ∧
      powerCut ρ (r+5) ≤ D ∧ powerCut γ (4*C*Real.log r) ≤ D ∧
      logCut γ (4*C*(3+2*ρ)) ≤ D ∧ powerCut (γ-σ) (2*C) ≤ D ∧
      logCut (1-2*ρ) (4*ρ) ≤ D := by
    simpa only [nibbleCut, C, γ, max_le_iff] using hD
  rcases bounds with ⟨hD2,h2,h4,h5,h7,hA,hB,hS,hL⟩
  have f2 := const_le_rpow (by positivity : 0 < 2*ρ) h2
  have f4 := const_le_rpow e4 h4
  have f5 := const_le_rpow e5 h5
  have f7 := const_le_rpow hρ h7
  have fA := const_le_rpow hγ0 hA
  have fB := mul_log_le_rpow hγ0 hB
  have fS : D^σ ≤ (1/(2*C))*D^γ := by
    apply rpow_le_mul_rpow hγσ (by positivity)
    simpa only [one_div_one_div] using hS
  have fL := mul_log_le_rpow e8 hL
  have hD0 : 0 < D := by linarith
  refine ⟨by linarith,f2,f4,f5,?_,f7,?_⟩
  · have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have h1 : Real.log r ≤ D^γ/(4*C) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2' : (3+2*ρ)*Real.log D ≤ D^γ/(4*C) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : D^σ ≤ D^γ/(2*C) := by
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using fS
    change Real.log r+(3+2*ρ)*Real.log D+D^σ ≤ D^γ/C
    have : D^γ/(4*C)+D^γ/(4*C)+D^γ/(2*C)=D^γ/C := by field_simp; ring
    linarith
  · have hpow : D^(1-2*ρ)*D^(2*ρ)=D := by rw [← Real.rpow_add hD0]; simp
    have hp : 0 < D^(2*ρ) := Real.rpow_pos_of_pos hD0 _
    have : 4*ρ*Real.log D*D^(2*ρ) ≤ D := by
      calc _ ≤ D^(1-2*ρ)*D^(2*ρ) := mul_le_mul_of_nonneg_right fL hp.le
        _ = D := hpow
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    nlinarith


theorem nibble_marginal_explicit (r : ℕ) (hr : 2 ≤ r) {ρ κ σ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hsum : (2 * r + 4) * ρ + κ + σ < 1) :
    ∀ D : ℝ, nibbleCut r ρ κ σ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0) := by
  intro D hD
  exact nibble_marginal_of_facts r hr hρ hκ hσ hsum D
    (nibbleFacts_explicit r (by omega) hρ hκ hσ hsum hD)

#print axioms nibbleFacts_explicit
#print axioms nibble_marginal_of_facts
#print axioms nibble_marginal_explicit
end Pseudorandom.Nibble
