module
public import RequestProject.TypedTriangle.PaschAdaptiveAssemblyCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open Vortex Vortex.IntrinsicRawPathsPreparedVortex

/-- Initialize the actual adaptive state from the literal exterior
decomposition and its full stored universe. The first child is small
relative to the original host; no new packing is selected here. -/
def TrackingState.initial
    {I V Orig Abs : Type} [Fintype V] [Fintype Orig] [Fintype Abs]
    {F : Set (Multiset I)} {α₀ q C : ℝ} {β : ℕ → ℝ}
    {h N M d T m : ℕ} {a εRoute t : ℝ} {H : Host V I} {μ : Finset V → ℝ}
    (chain : IntrinsicRawPathsPreparedVortex F α₀ q C β h N M d T m a εRoute t H μ)
    (Cactual αactual ζState : ℝ) (HOrig : Host Orig I) (HAbs : Host Abs I)
    (eOut : Abs ↪ Orig) (R : Finset (Sym2 Abs)) (base : Finset (Finset Orig))
    (Uterminal : Finset Abs) (cost τ qOuter : ℝ) (Lbase stepCodegree : ℕ)
    (actual : ActualState chain Cactual αactual ζState)
    (eAbs : Survivors chain.head.trim ↪ Abs)
    (prefixData : PaidPrefix HOrig F (embeddedEdges eOut R) actual.host (eAbs.trans eOut))
    (available : Finset (Finset Orig))
    (hPair : PairCodegreeBound available Lbase)
    (hTriples : ∀ Q ∈ available, Q.card = 3)
    (hBase : base ⊆ prefixData.paid) (hPaid : prefixData.paid ⊆ available)
    (hAdj : ∀ u v, actual.host.G.Adj u v → HAbs.G.Adj (eAbs u) (eAbs v))
    (hLab : ∀ u, actual.host.lab u = HAbs.lab (eAbs u))
    (hTerminal : chain.terminalWindow.map eAbs ⊆ Uterminal)
    (hCost : 0 ≤ cost)
    (hFirst : (Fintype.card (Survivors chain.head.trim) : ℝ) ≤
      2*qOuter*Fintype.card Orig)
    (hOuter : (count available : ℝ) ≤ count base+(τ/2)*(Fintype.card Orig : ℝ)^2)
    (hRate : 8*cost*qOuter ≤ τ) :
    TrackingState chain Cactual αactual ζState HOrig HAbs eOut R base Uterminal cost τ Lbase stepCodegree := by
  have hDepth : Fintype.card (Survivors chain.head.trim) ≤ Fintype.card Orig :=
    Fintype.card_le_of_injective (eAbs.trans eOut) (eAbs.trans eOut).injective
  have hRemaining := initial_remaining_budget_le cost (Fintype.card Orig) qOuter
    (Fintype.card (Survivors chain.head.trim)) hCost (by positivity) hFirst
  have hRatePaid := mul_le_mul_of_nonneg_right hRate (sq_nonneg (Fintype.card Orig : ℝ))
  refine {
    actual := actual
    eAbs := eAbs
    prefixData := prefixData
    available := available
    codegree := Lbase
    depth := 0
    pair_bound := hPair
    triples := hTriples
    base_paid := hBase
    paid_available := hPaid
    codegree_bound := by simp
    depth_bound := by simpa only [pow_zero,one_mul] using hDepth
    budget := ?_
    map_adj := hAdj
    map_lab := hLab
    terminal_subset := hTerminal
  }
  linarith only [hOuter,hRemaining,hRatePaid]

#print axioms TrackingState.initial
end TypedTriangle.Pasch
