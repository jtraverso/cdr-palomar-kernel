module
public import RequestProject.TypedTriangle.ExplicitStructuredCleanLayer
public import RequestProject.TypedTriangle.ExplicitScheduledRawProfileBudget
public import RequestProject.TypedTriangle.VortexConcreteInnerLayers
public import RequestProject.TypedTriangle.VortexConcreteOuterLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex.Explicit
open IntrinsicRawPathsPreparedVortex CatalogNative CorePaid BasalIncidence
def innerLayerOrder (α C q a : ℝ) (h m L : ℕ) (K εRef γRef : ℕ → ℝ)
    (nRef nPaid : ℕ → ℕ) (nGeometry : ℕ) : ℕ :=
  let nRun : Fin (L+1) → ℕ := fun j => cleanLayerThreshold (α/16) C (α/32)
    (γRef j) q (α/4) (windowRouteRate a q m/4) h (m+1) (nRef j) (nPaid j) nGeometry
  max 1 (max (univ.sup nRun) (max (scheduledProfileOrder C K εRef L) ⌈2/q⌉₊))

def outerLayerTerminalBudget (α C qOuter aOuter : ℝ) (h m L : ℕ) (γRef : ℕ → ℝ) : ℝ :=
  (univ : Finset (Fin (L+1))).inf' (by simp) (fun j =>
    layerTerminalBudget (α/16) (2*C) (α/32) (γRef j) qOuter (α/4)
      (windowRouteRate (aOuter/2) qOuter m/4) h (m+1))

def outerLayerOrder (α C qOuter aOuter : ℝ) (h m L : ℕ)
    (γRef : ℕ → ℝ) (nRef nPaid : ℕ → ℕ) (nGeometry : ℕ) : ℕ :=
  let nRun : Fin (L+1) → ℕ := fun j => cleanLayerThreshold (α/16) C (α/32)
    (γRef j) qOuter (α/4) (windowRouteRate (aOuter/2) qOuter m/4)
    h (m+1) (nRef j) (nPaid j) nGeometry
  max 1 (max (univ.sup nRun) ⌈2/qOuter⌉₊)

theorem innerLayerOrder_pos (α C q a : ℝ) (h m L : ℕ) (K εRef γRef : ℕ → ℝ)
    (nRef nPaid : ℕ → ℕ) (nGeometry : ℕ) :
    1 ≤ innerLayerOrder α C q a h m L K εRef γRef nRef nPaid nGeometry :=
  le_max_left _ _

theorem outerLayerOrder_pos (α C qOuter aOuter : ℝ) (h m L : ℕ)
    (γRef : ℕ → ℝ) (nRef nPaid : ℕ → ℕ) (nGeometry : ℕ) :
    1 ≤ outerLayerOrder α C qOuter aOuter h m L γRef nRef nPaid nGeometry :=
  le_max_left _ _

theorem outerLayerTerminalBudget_pos (α C qOuter aOuter : ℝ) (h m L : ℕ)
    (γRef : ℕ → ℝ) (hα : 0 < α) (hC : 1 ≤ C) (hq : 0 < qOuter)
    (ha : 0 < aOuter) (hγ : ∀ j ≤ L, 0 < γRef j) :
    0 < outerLayerTerminalBudget α C qOuter aOuter h m L γRef := by
  apply (lt_inf'_iff _).mpr
  intro j _
  exact layerTerminalBudget_pos (α/16) (2*C) (α/32) (γRef j)
    qOuter (α/4) (windowRouteRate (aOuter/2) qOuter m/4) h (m+1)
    (by positivity) (by linarith) (by positivity) (hγ j (Nat.le_of_lt_succ j.isLt))
    hq (by positivity) (div_pos (windowRouteRate_pos m (half_pos ha) hq) (by norm_num))


end TypedTriangle.Vortex.Explicit
