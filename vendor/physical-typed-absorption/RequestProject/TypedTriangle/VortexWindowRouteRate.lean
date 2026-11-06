/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexWindowPathPayment
public import RequestProject.S07V27.CoreComponent
public import RequestProject.S07V45.CoreContract
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24 S07V45
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

def windowRouteRate (a q : ℝ) (m : ℕ) : ℝ :=
  a*q/(32*((m : ℝ)+1)*4^m)

theorem windowRouteRate_pos {a q : ℝ} (m : ℕ) (ha : 0 < a) (hq : 0 < q) :
    0 < windowRouteRate a q m := by unfold windowRouteRate; positivity

/-- The path counts retained on the actual window give a robust route
budget linear in the sampling rate. No ambient-order influence bound is used. -/
theorem routeProp_of_window_path_count {V I : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (W : Finset V) (a q : ℝ) (m : ℕ) (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (W.card : ℝ) ≤ 2*q*Fintype.card V)
    (hPaths : ∀ v x y, OrigAdm G lab F v x y →
      a*(Fintype.card V : ℝ)^m*q^m/4 ≤
        (pathsIn (ComponentRows.link G lab F v) m x y W).card) :
    S07V27.RouteProp G lab F (m+1) (windowRouteRate a q m) W := by
  intro Z B _ b hZ hB hb v x y hxy
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty V from ⟨v⟩)
  have hRate : 0 < windowRouteRate a q m := windowRouteRate_pos m ha hq
  have hWplus : (W.card : ℝ)+2 ≤ 4*q*Fintype.card V := by nlinarith
  have hWfour : (W.card : ℝ) ≤ 4*q*Fintype.card V := by nlinarith
  have hNumeric : ((Z.card*m*W.card^(m-1) + (m+1)*b*(W.card+2)^(m-1) : ℕ) : ℝ) ≤
      windowRouteRate a q m*Fintype.card V*(2*((m : ℝ)+1))*
        (4*q*Fintype.card V)^(m-1) := by
    push_cast
    calc
      _ ≤ (windowRouteRate a q m*Fintype.card V)*(m : ℝ)*
            (4*q*Fintype.card V)^(m-1) +
          ((m : ℝ)+1)*(windowRouteRate a q m*Fintype.card V)*
            (4*q*Fintype.card V)^(m-1) := by gcongr
      _ = windowRouteRate a q m*Fintype.card V*(2*(m : ℝ)+1)*
          (4*q*Fintype.card V)^(m-1) := by ring
      _ ≤ _ := by gcongr <;> linarith
  have hIdentity : windowRouteRate a q m*Fintype.card V*(2*((m : ℝ)+1))*
      (4*q*Fintype.card V)^(m-1) =
        a*(Fintype.card V : ℝ)^m*q^m/64 := by
    have hExp : m = (m-1)+1 := by omega
    have hN : (Fintype.card V : ℝ)^m =
        (Fintype.card V : ℝ)^(m-1)*Fintype.card V := by
      conv_lhs => rw [hExp]
      rw [pow_succ]
    have hQ : q^m = q^(m-1)*q := by
      conv_lhs => rw [hExp]
      rw [pow_succ]
    have hFour : (4 : ℝ)^m = 4^(m-1)*4 := by
      conv_lhs => rw [hExp]
      rw [pow_succ]
    rw [windowRouteRate,mul_pow,mul_pow,hN,hQ,hFour]
    field_simp
    ring
  have hScale : 0 < a*(Fintype.card V : ℝ)^m*q^m := by positivity
  have hStrict : a*(Fintype.card V : ℝ)^m*q^m/64 <
      a*(Fintype.card V : ℝ)^m*q^m/4 := by linarith
  exact pay_deterministic_on_window (ComponentRows.link G lab F v) m x y W
    (hPaths v x y hxy) Z B b hB (hNumeric.trans_lt (hIdentity.trans_lt hStrict))

#print axioms windowRouteRate_pos
#print axioms routeProp_of_window_path_count
end TypedTriangle.Vortex
