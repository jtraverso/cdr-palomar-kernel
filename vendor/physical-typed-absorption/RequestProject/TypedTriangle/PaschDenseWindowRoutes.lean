module
public import RequestProject.TypedTriangle.VortexWindowRouteRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open TypedTriangle.Vortex

def validWindowPaths {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V)
    (W Z : Finset V) (B : SimpleGraph V) : Finset (G.Walk x y) :=
  (pathsIn G m x y W).filter (fun p =>
    (∀ i : Fin m, intl m p i ∉ Z) ∧
      ∀ k < m+1, ¬ B.Adj (p.getVert k) (p.getVert (k+1)))

/-- Retain the count of valid paths, instead of merely selecting one path.
These are the same vertex and edge losses as the existing route constructor. -/
theorem validWindowPaths_card_loss {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V)
    (W Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hB : ∀ v, B.degree v ≤ d) :
    (pathsIn G m x y W).card ≤ (validWindowPaths G m x y W Z B).card +
      (Z.card*m*W.card^(m-1) + (m+1)*d*(W.card+2)^(m-1)) := by
  let A := pathsIn G m x y W
  let BadV := A.filter (fun p => ∃ i : Fin m, intl m p i ∈ Z)
  let BadE := A.filter (fun p => ∃ k ∈ range (m+1), B.Adj (p.getVert k) (p.getVert (k+1)))
  have hLength : ∀ p ∈ A, p.length = m+1 := by
    intro p hp
    exact SimpleGraph.mem_finsetWalkLength_iff.mp (mem_filter.mp (mem_filter.mp hp).1).1
  have hInternal : ∀ p ∈ A, intlSet m p ⊆ W := fun p hp => (mem_filter.mp hp).2
  have hV := card_through_window_le m x y A W Z hLength hInternal
  have hE := card_edge_window_le m x y A W hLength hInternal B d hB
  have hCover : A ⊆ validWindowPaths G m x y W Z B ∪ (BadV ∪ BadE) := by
    intro p hp
    by_cases hVbad : ∃ i : Fin m, intl m p i ∈ Z
    · have hBad : p ∈ BadV := by simpa only [BadV,mem_filter] using And.intro hp hVbad
      exact mem_union_right _ (mem_union_left _ hBad)
    by_cases hEbad : ∃ k ∈ range (m+1), B.Adj (p.getVert k) (p.getVert (k+1))
    · have hBad : p ∈ BadE := by simpa only [BadE,mem_filter] using And.intro hp hEbad
      exact mem_union_right _ (mem_union_right _ hBad)
    have hVert : ∀ i : Fin m, intl m p i ∉ Z := fun i hi => hVbad ⟨i,hi⟩
    have hEdge : ∀ k < m+1, ¬ B.Adj (p.getVert k) (p.getVert (k+1)) :=
      fun k hk hAdj => hEbad ⟨k,mem_range.mpr hk,hAdj⟩
    have hGood : p ∈ validWindowPaths G m x y W Z B := by
      simpa only [validWindowPaths,mem_filter] using And.intro hp (And.intro hVert hEdge)
    exact mem_union_left _ hGood
  have hCount : A.card ≤ (validWindowPaths G m x y W Z B).card + (BadV.card+BadE.card) :=
    (card_le_card hCover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
  apply hCount.trans
  apply Nat.add_le_add_left
  apply Nat.add_le_add hV
  convert hE using 1 <;> congr 1 <;> ext p <;> simp only [mem_filter]

theorem dense_validWindowPaths {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (a q : ℝ) (m : ℕ)
    (x y : V) (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V) (hWindow : (W.card : ℝ) ≤ 2*q*Fintype.card V)
    (hPaths : a*(Fintype.card V : ℝ)^m*q^m/4 ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ)
    (hZ : (Z.card : ℝ) ≤ windowRouteRate a q m*Fintype.card V)
    (hB : ∀ v, B.degree v ≤ b) (hb : (b : ℝ) ≤ windowRouteRate a q m*Fintype.card V) :
    a*(Fintype.card V : ℝ)^m*q^m/8 ≤ (validWindowPaths G m x y W Z B).card := by
  have hRate : 0 < windowRouteRate a q m := windowRouteRate_pos m ha hq
  have hWplus : (W.card : ℝ)+2 ≤ 4*q*Fintype.card V := by nlinarith only [hWindow,hOrder]
  have hWfour : (W.card : ℝ) ≤ 4*q*Fintype.card V := by nlinarith only [hWindow,hOrder]
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
      (4*q*Fintype.card V)^(m-1) = a*(Fintype.card V : ℝ)^m*q^m/64 := by
    have hExp : m = (m-1)+1 := by omega
    have hN : (Fintype.card V : ℝ)^m = (Fintype.card V : ℝ)^(m-1)*Fintype.card V := by
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
  have hCount := validWindowPaths_card_loss G m x y W Z B b hB
  have hCountR : ((pathsIn G m x y W).card : ℝ) ≤
      (validWindowPaths G m x y W Z B).card +
        ((Z.card*m*W.card^(m-1) + (m+1)*b*(W.card+2)^(m-1) : ℕ) : ℝ) := by
    exact_mod_cast hCount
  have hLoss := hNumeric.trans_eq hIdentity
  have hScale : 0 ≤ a*(Fintype.card V : ℝ)^m*q^m := by positivity
  nlinarith only [hPaths,hCountR,hLoss,hScale]

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.validWindowPaths_card_loss
#print axioms TypedTriangle.Pasch.dense_validWindowPaths
