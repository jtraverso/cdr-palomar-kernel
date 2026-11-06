/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativePreparedTerminalAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex

/-- The terminal bound is fixed before choosing the outer sampling rate.
The universal absorber then avoids the entire first core, so it can be
reserved before packing while every deeper induced core stays untouched. -/
theorem terminal_absorber_avoiding_outer_core (α β : ℝ) (h t : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1/32 ∧ ∃ K N n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h N β →
        ∀ W U : Finset V, (W.card : ℝ) ≤ 2*q*Fintype.card V →
          U.card ≤ t →
          ∃ R : Finset (Sym2 V), Disjoint R (triEdges W) ∧
            R.card ≤ K ∧ (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ L : Finset (Sym2 V), IsPhysical H F L → support L ⊆ U →
              Basal H F (R ∪ L) := by
  obtain ⟨ε,hε,K,N,n₀,hReserve⟩ :=
    PreparedSupply.terminal_absorber_on_prepared_host α β h t hα hβ
  let q := min (1/64) (ε/4)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hqSmall : q ≤ 1/32 := (min_le_left _ _).trans (by norm_num)
  have hBudget : 2*q ≤ ε := by
    have h := min_le_right (1/64 : ℝ) (ε/4)
    dsimp only [q]
    linarith
  refine ⟨q,hq,hqSmall,K,N,n₀,?_⟩
  intro V I _ H F hn Pc W U hW hU
  have hBcap : (W.card : ℝ) ≤ ε*Fintype.card V :=
    hW.trans (by
      have h := mul_le_mul_of_nonneg_right hBudget
        (show (0 : ℝ) ≤ Fintype.card V by positivity)
      nlinarith)
  obtain ⟨R,hAvoid,-,hCard,hDeg,hBasal,hAbsorb⟩ :=
    hReserve H F hn Pc U (triEdges W) W.card hU
      (fun v => S07V31.degIn_triEdges_le W v) hBcap
  exact ⟨R,hAvoid,hCard,hDeg,hBasal,hAbsorb⟩

#print axioms terminal_absorber_avoiding_outer_core
end TypedTriangle.Vortex
