/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicRawPreparedVortex
public import RequestProject.TypedTriangle.VortexNestedLatticeTransport
public import RequestProject.TypedTriangle.VortexCleanHingeEquiv
public import RequestProject.TypedTriangle.VortexRawProfileEquiv
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TypedTriangle.Vortex

/-- The actual restricted raw weights stored at a prepared node. -/
def preparedRawWeights {X I : Type} [Fintype X]
    {H : Host X I} {F : Set (Multiset I)} {α C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α C β h N M d T μ) :
    Finset (Survivors node.trim) → ℝ := RawReference.restrictedWeights μ node.trim

/-- The real finite schedule may lower the retained prepared order; no new
preparation or stronger core hypothesis is needed. -/
theorem preparedCore_lower_order {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (α β : ℝ) (h N Nreq : ℕ)
    (P : Dispersal.PreparedCore H.G H.lab F α h N β) (hN : Nreq ≤ N) :
    Dispersal.PreparedCore H.G H.lab F α h Nreq β :=
  ⟨P.h3,P.h4,fun Z hZ => hN.trans (P.order Z hZ),P.lattice_persist⟩

/-- All prepared and approximate raw data are carried from the actual raw
node to its literal window; H1 is still approximate at this stage. -/
theorem raw_prepared_layer_window_data {X Y I : Type} [Fintype X] [Fintype Y]
    {F : Set (Multiset I)} {H : Host X I} {α₀ C : ℝ} {β : ℕ → ℝ}
    {h N M d T : ℕ} {μ : Finset X → ℝ}
    (node : IntrinsicRawPreparedLayer H F α₀ C β h N M d T μ)
    (e : Survivors node.trim ≃ Y) (J : Host Y I)
    (hAdj : ∀u v, (restrictedHost H node.trim).G.Adj u v ↔ J.G.Adj (e u) (e v))
    (hLab : ∀u, (restrictedHost H node.trim).lab u = J.lab (e u)) :
    Dispersal.PreparedCore J.G J.lab F (α₀/8) h N (β node.index) ∧
    CommonNbrCond J F (α₀/4) ∧ CleanHingeCond J F (α₀/4) h ∧
    RawProfileAt J F C
      (globalRawProfileError 4 (max 1 (2*C)) β (Fintype.card (Survivors node.trim)) node.index)
      (equivSeed e.symm (preparedRawWeights node)) := by
  have hαEq : (α₀/4)/2 = α₀/8 := by ring
  have hP := preparedCore_equiv e (restrictedHost H node.trim) J F
    ((α₀/4)/2) h N (β node.index) hAdj hLab node.prepared
  have hAdjInv : ∀u v, J.G.Adj u v ↔
      (restrictedHost H node.trim).G.Adj (e.symm u) (e.symm v) := by
    intro u v
    simpa only [e.apply_symm_apply] using (hAdj (e.symm u) (e.symm v)).symm
  have hLabInv : ∀u, J.lab u = (restrictedHost H node.trim).lab (e.symm u) := by
    intro u
    simpa only [e.apply_symm_apply] using (hLab (e.symm u)).symm
  refine ⟨by simpa only [hαEq] using hP,
    commonNbrCond_equiv e _ J F (α₀/4) hAdj hLab node.h3,
    cleanHingeCond_equiv e _ J F (α₀/4) h hAdj hLab node.clean,?_⟩
  exact raw_profile_pull_equiv e.symm J (restrictedHost H node.trim) F C _
    (RawReference.restrictedWeights μ node.trim) hAdjInv hLabInv node.raw

/-- The globally retained quarter-error cap is exactly the coefficient
window of the paid child consumer. -/
theorem quarter_raw_profile_weights {X I : Type} [Fintype X]
    (H : Host X I) (F : Set (Multiset I)) (C ρ : ℝ) (μ : Finset X → ℝ)
    (hC : 1 ≤ C) (hρ : ρ ≤ 1/4) (hRaw : RawProfileAt H F C ρ μ) :
    ∀ Q, IsAllowed H F Q → (3/(4*C))/Fintype.card X ≤ μ Q ∧
      μ Q ≤ (5*C/4)/Fintype.card X := by
  have hCpos : 0 < C := by linarith
  intro Q hQ
  have hLo : 3/(4*C) ≤ (1-ρ)/C := by
    have hd := div_le_div_of_nonneg_right (show (3/4:ℝ) ≤ 1-ρ by linarith) hCpos.le
    convert hd using 1 <;> field_simp <;> ring
  have hHi : (1+ρ)*C ≤ 5*C/4 := by nlinarith
  exact ⟨(div_le_div_of_nonneg_right hLo (by positivity)).trans (hRaw.1 Q hQ).1,
    (hRaw.1 Q hQ).2.trans (div_le_div_of_nonneg_right hHi (by positivity))⟩

#print axioms preparedCore_lower_order
#print axioms raw_prepared_layer_window_data
#print axioms quarter_raw_profile_weights
end TypedTriangle.Vortex
