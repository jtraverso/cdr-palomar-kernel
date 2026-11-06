module
public import RequestProject.TypedTriangle.PaschWindowPathAssignments
public import RequestProject.TypedTriangle.PaschSupportPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V : Type} [Fintype V] [DecidableEq V]

def fanPathCoordinates {m : ℕ} (x y : V) (f : Fin m → V) : Fin (m+2) → V :=
  Fin.cons x (Fin.snoc f y)

def fanTriangle {m : ℕ} (v x y : V) (f : Fin m → V) (k : Fin (m+1)) : Finset V :=
  {v,fanPathCoordinates x y f k.castSucc,fanPathCoordinates x y f k.succ}

def fanCompletionCost {m : ℕ} (R : Finset (Finset V)) (v x y : V) (f : Fin m → V) : ℕ :=
  ∑ k : Fin (m+1), rootedCount (insert (fanTriangle v x y f k) R) (fanTriangle v x y f k)

private theorem fanTriangle_zero {m : ℕ} (v x y : V) (f : Fin (m+1) → V) :
    fanTriangle v x y f 0 = {v,x,f 0} := by
  simp [fanTriangle,fanPathCoordinates]

private theorem fanTriangle_succ {m : ℕ} (v x y : V) (f : Fin m → V) (j : Fin m) :
    fanTriangle v x y f j.succ = {v,f j,(Fin.snoc f y : Fin (m+1) → V) j.succ} := by
  have hIndex : j.succ.castSucc = j.castSucc.succ := by apply Fin.ext; rfl
  simp only [fanTriangle,fanPathCoordinates,hIndex,Fin.cons_succ,Fin.snoc_castSucc]

/-- Every actual fan edge has an internal free coordinate, including the
two endpoint edges. The direct-edge case m=0 is explicitly excluded. -/
theorem fan_triangle_has_free_coordinate (m : ℕ) (hm : 0 < m) (v x y : V)
    (k : Fin (m+1)) :
    ∃ j : Fin m, ∃ other : ({i : Fin m // i ≠ j} → V) → V,
      ∀ f : Fin m → V, fanTriangle v x y f k =
        {v,other (fun i => f i.val),f j} := by
  cases m with
  | zero => omega
  | succ s =>
    refine Fin.cases ?_ (fun j => ?_) k
    · refine ⟨0,fun _ => x,?_⟩
      intro f
      exact fanTriangle_zero v x y f
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · refine ⟨Fin.last s,fun _ => y,?_⟩
        intro f
        rw [fanTriangle_succ,Fin.succ_last,Fin.snoc_last]
        ext a
        simp [or_comm,or_left_comm,or_assoc]
      · have hNe : i.succ ≠ i.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ,Fin.val_castSucc] at hv
          omega
        refine ⟨i.castSucc,fun r => r ⟨i.succ,hNe⟩,?_⟩
        intro f
        rw [fanTriangle_succ]
        have hIndex : i.castSucc.succ = i.succ.castSucc := by apply Fin.ext; rfl
        rw [hIndex,Fin.snoc_castSucc]
        ext a
        simp [or_comm,or_left_comm,or_assoc]

/-- One assignment from the same valid family pays all m+1 fan triangles
at once. No triangle is selected using a different assignment. -/
theorem exists_low_fan_assignment (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (v x y : V) (m : ℕ) (hm : 0 < m)
    (P : Finset (Fin m → V)) (κ : ℝ) (hκ : 0 < κ)
    (hP : κ*(Fintype.card V : ℝ)^m ≤ P.card) :
    ∃ f ∈ P, (fanCompletionCost R v x y f : ℝ) ≤ ((m+1 : ℕ) : ℝ)*(L : ℝ)^3/κ := by
  choose i other hForm using (fun k : Fin (m+1) => fan_triangle_has_free_coordinate m hm v x y k)
  have hnV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hN : 0 < (Fintype.card (Fin m → V) : ℝ) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
    exact pow_pos (by exact_mod_cast hnV) m
  have hDensity : κ*(Fintype.card (Fin m → V) : ℝ) ≤ P.card := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using hP
  obtain ⟨f,hf,hCost⟩ := exists_low_support_potential R L hL i (fun _ _ => v) other P κ hκ hN hDensity
  have hEq : supportCompletionCost R i (fun _ _ => v) other f = fanCompletionCost R v x y f := by
    unfold supportCompletionCost fanCompletionCost
    apply sum_congr rfl
    intro k _
    rw [hForm k f]
  rw [hEq] at hCost
  exact ⟨f,hf,by simpa only [Fintype.card_fin] using hCost⟩

/-- The weighted assignment is reconstructed into its actual retained walk.
All forbidden-vertex and forbidden-edge conditions of validWindowPaths remain. -/
theorem exists_low_cost_valid_window_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 0 < m) (v x y : V) (W Z : Finset V) (B : SimpleGraph V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (κ : ℝ) (hκ : 0 < κ)
    (hCount : κ*(Fintype.card V : ℝ)^m ≤ (validWindowPaths G m x y W Z B).card) :
    ∃ p ∈ validWindowPaths G m x y W Z B,
      ((∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)}) : ℝ) ≤
          ((m+1 : ℕ) : ℝ)*(L : ℝ)^3/κ := by
  have hP : κ*(Fintype.card V : ℝ)^m ≤ (windowPathAssignments G m x y W Z B).card := by
    simpa only [windowPathAssignments_card] using hCount
  obtain ⟨f,hf,hCost⟩ := exists_low_fan_assignment R L hL v x y m hm
    (windowPathAssignments G m x y W Z B) κ hκ hP
  obtain ⟨p,hp,hCoordinates⟩ := windowPathAssignments_realize G m x y W Z B hf
  have hEq : fanCompletionCost R v x y f = ∑ k : Fin (m+1), rootedCount
      (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
      {v,p.getVert k.val,p.getVert (k.val+1)} := by
    unfold fanCompletionCost
    apply sum_congr rfl
    intro k _
    have hT : fanTriangle v x y f k = {v,p.getVert k.val,p.getVert (k.val+1)} := by
      unfold fanTriangle fanPathCoordinates
      rw [hCoordinates]
      rfl
    rw [hT]
  exact ⟨p,hp,by simpa only [hEq,Nat.cast_sum] using hCost⟩

/-- The actual large-sample path count and the legacy deletion budget
produce the low-cost walk; no path-family provider is assumed here. -/
theorem exists_low_cost_dense_window_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (a q : ℝ) (m : ℕ) (v x y : V)
    (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V) (hWindow : (W.card : ℝ) ≤ 2*q*Fintype.card V)
    (hPaths : a*(Fintype.card V : ℝ)^m*q^m/4 ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ)
    (hZ : (Z.card : ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (hB : ∀ z, B.degree z ≤ b) (hb : (b : ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) :
    ∃ p ∈ validWindowPaths G m x y W Z B,
      ((∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)}) : ℝ) ≤
          8*((m+1 : ℕ) : ℝ)*(L : ℝ)^3/(a*q^m) := by
  have hDense := dense_validWindowPaths G W a q m x y ha hq hm hOrder hWindow hPaths Z B b hZ hB hb
  have hκ : 0 < a*q^m/8 := by positivity
  have hCount : (a*q^m/8)*(Fintype.card V : ℝ)^m ≤
      (validWindowPaths G m x y W Z B).card := by
    convert hDense using 1 <;> ring
  obtain ⟨p,hp,hCost⟩ := exists_low_cost_valid_window_path G m hm v x y W Z B R L hL
    (a*q^m/8) hκ hCount
  refine ⟨p,hp,?_⟩
  convert hCost using 1 <;> field_simp [ne_of_gt ha,pow_ne_zero m (ne_of_gt hq)] <;> ring

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.fan_triangle_has_free_coordinate
#print axioms TypedTriangle.Pasch.exists_low_fan_assignment
#print axioms TypedTriangle.Pasch.exists_low_cost_valid_window_path
#print axioms TypedTriangle.Pasch.exists_low_cost_dense_window_path
