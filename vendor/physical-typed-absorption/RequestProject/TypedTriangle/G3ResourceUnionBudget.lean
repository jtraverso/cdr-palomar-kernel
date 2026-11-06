/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3UniformResources
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Pay the degree of all four protected resource families in the window of a
dense sampled-core reference. This is the arithmetic bridge, independent of
the particular way the four families were constructed. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open SelSimul

theorem four_resource_reference_window {V : Type} [Fintype V]
    (W : Finset V) (A B C D : Finset (Sym2 V))
    (q γ ρ τ ηT ε : ℝ)
    (hq : 0 < q) (hγ : 0 < γ)
    (hW : q*Fintype.card V/2 ≤ W.card)
    (hSum : ρ+τ+ηT ≤ γ*q/8) (hε : ε ≤ γ/4)
    (hA : ∀ v, (degIn A v:ℝ) ≤ ρ*Fintype.card V)
    (hB : ∀ v, (degIn B v:ℝ) ≤ τ*Fintype.card V)
    (hC : ∀ v, (degIn C v:ℝ) ≤ ηT*Fintype.card V)
    (hD : ∀ v, (degIn D v:ℝ) ≤ ε*W.card)
    (hLarge : 2 ≤ γ*W.card) :
    ∃ dB : ℕ, (∀ v, degIn (((A∪B)∪C)∪D) v ≤ dB) ∧
      (dB:ℝ) ≤ γ*W.card := by
  let dB := ⌈γ*W.card/2⌉₊
  refine ⟨dB,?_,?_⟩
  · intro v
    have hAB := edeg_union_le A B v
    have hABC := edeg_union_le (A∪B) C v
    have hABCD := edeg_union_le ((A∪B)∪C) D v
    change degIn (A∪B) v ≤ degIn A v+degIn B v at hAB
    change degIn ((A∪B)∪C) v ≤ degIn (A∪B) v+degIn C v at hABC
    change degIn (((A∪B)∪C)∪D) v ≤ degIn ((A∪B)∪C) v+degIn D v at hABCD
    have hu : (degIn (((A∪B)∪C)∪D) v:ℝ) ≤
        degIn A v+degIn B v+degIn C v+degIn D v := by
      exact_mod_cast (show degIn (((A∪B)∪C)∪D) v ≤
        degIn A v+degIn B v+degIn C v+degIn D v by omega)
    have hN : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hW0 : (0:ℝ) ≤ W.card := Nat.cast_nonneg _
    have hsumN := mul_le_mul_of_nonneg_right hSum hN
    have hεW := mul_le_mul_of_nonneg_right hε hW0
    have hγW := mul_le_mul_of_nonneg_left hW hγ.le
    have hHalf : (degIn (((A∪B)∪C)∪D) v:ℝ) ≤ γ*W.card/2 := by
      nlinarith only [hu,hA v,hB v,hC v,hD v,hsumN,hεW,hγW]
    exact_mod_cast hHalf.trans (Nat.le_ceil _)
  · have hceil : (dB:ℝ) < γ*W.card/2+1 :=
      Nat.ceil_lt_add_one (by positivity : 0 ≤ γ*W.card/2)
    dsimp only [dB] at hceil ⊢
    linarith

#print axioms four_resource_reference_window

end TypedTriangle.CatalogNative
