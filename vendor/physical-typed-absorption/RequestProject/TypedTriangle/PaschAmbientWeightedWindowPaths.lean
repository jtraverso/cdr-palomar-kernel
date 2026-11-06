module
public import RequestProject.TypedTriangle.PaschRelativeWeightedWindowPaths
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace TypedTriangle.Pasch
variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem fanPathCoordinates_map (e : V→A) {m : ℕ} (x y : V) (f : Fin m→V) :
    fanPathCoordinates (e x) (e y) (fun j => e (f j)) =
      fun j => e (fanPathCoordinates x y f j) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [fanPathCoordinates]
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [fanPathCoordinates]
    · simp [fanPathCoordinates]

/-- The same window family pays against an arbitrary AMBIENT previous
universe. Only its free coordinate is restricted to W; its rooted triangles
are mapped literally along e. The ambient/window ratio is retained. -/
theorem exists_low_cost_ambient_relative_window_path
    (e : V↪A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 0 < m) (v x y : V) (W Z : Finset V) (B : SimpleGraph V)
    (R : Finset (Finset A)) (L : ℕ) (hL : PairCodegreeBound R L)
    (κ : ℝ) (hκ : 0 < κ) (hW : 0 < (W.card:ℝ))
    (hCount : κ*(W.card:ℝ)^m ≤ (validWindowPaths G m x y W Z B).card) :
    ∃p∈validWindowPaths G m x y W Z B,
      ((∑k:Fin (m+1),rootedCount
        (insert {e v,e (p.getVert k.val),e (p.getVert (k.val+1))} R)
        {e v,e (p.getVert k.val),e (p.getVert (k.val+1))}):ℝ)  ≤ 
      ((Fintype.card A:ℝ)/W.card)*(((m+1:ℕ):ℝ)*(L:ℝ)^3)/κ := by
  let P := windowPathAssignments G m x y W Z B
  have hSupp : ∀f∈P, ∀j:Fin m, f j∈W := windowPathAssignments_supported G m x y W Z B
  let PW := restrictedAssignments P W hSupp
  let eW : W↪A := (Function.Embedding.subtype (fun z => z∈W)).trans e
  have hDensity : κ*(Fintype.card (Fin m→W):ℝ) ≤ PW.card := by
    simpa only [PW,restrictedAssignments_card,P,windowPathAssignments_card,
      Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow] using hCount
  choose i other hForm using (fun k:Fin (m+1) => 
    fan_triangle_has_free_coordinate m hm (e v) (e x) (e y) k)
  let otherW : ∀k, ({j:Fin m // j≠i k}→W)→A :=
    fun k r => other k (fun j => e ((r j).val))
  have hnW : 0 < (Fintype.card W:ℝ) := by simpa only [Fintype.card_coe] using hW
  obtain ⟨g,hg,hCost⟩ := exists_low_embedded_support_potential eW R L hL i
    (fun _ _ => e v) otherW PW κ hκ hnW hDensity
  let f : Fin m→V := fun j => (g j).val
  have hf : f∈P := restrictedAssignments_project P W hSupp hg
  have hFan : embeddedSupportCompletionCost eW R i (fun _ _ => e v) otherW g =
      fanCompletionCost R (e v) (e x) (e y) (fun j => e (f j)) := by
    unfold embeddedSupportCompletionCost fanCompletionCost
    apply sum_congr rfl
    intro k _
    have ht := congrArg (fun Q => rootedCount (insert Q R) Q)
      (hForm k (fun j => e (f j))).symm
    change rootedCount (insert {e v,other k (fun j => e ((g j.val).val)),e ((g (i k)).val)} R)
      {e v,other k (fun j => e ((g j.val).val)),e ((g (i k)).val)} = _
    exact ht
  obtain ⟨p,hp,hCoordinates⟩ := windowPathAssignments_realize G m x y W Z B hf
  have hMapCoordinates : fanPathCoordinates (e x) (e y) (fun j => e (f j)) =
      fun j:Fin (m+2) => e (p.getVert j.val) := by
    rw [fanPathCoordinates_map]
    exact congrArg (fun r:Fin (m+2)→V => fun j => e (r j)) hCoordinates
  have hWalk : fanCompletionCost R (e v) (e x) (e y) (fun j => e (f j)) =
      ∑k:Fin (m+1),rootedCount
        (insert {e v,e (p.getVert k.val),e (p.getVert (k.val+1))} R)
        {e v,e (p.getVert k.val),e (p.getVert (k.val+1))} := by
    unfold fanCompletionCost
    apply sum_congr rfl
    intro k _
    have hT : fanTriangle (e v) (e x) (e y) (fun j => e (f j)) k =
        {e v,e (p.getVert k.val),e (p.getVert (k.val+1))} := by
      unfold fanTriangle
      rw [hMapCoordinates]
      rfl
    rw [hT]
  exact ⟨p,hp,by simpa only [hFan,hWalk,Nat.cast_sum,Fintype.card_coe,Fintype.card_fin] using hCost⟩

/-- The relative density constant is independent of the sampling rate,
including when the previous triangles live in a larger ambient carrier. -/
theorem exists_low_cost_ambient_relative_dense_window_path
    (e : V↪A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (a q : ℝ) (m : ℕ) (v x y : V)
    (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (W.card:ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (W.card:ℝ))
    (hPaths : a*(Fintype.card V:ℝ)^m*q^m/4 ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ)
    (hZ : (Z.card:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (hB : ∀z, B.degree z ≤ b) (hb : (b:ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (R : Finset (Finset A)) (L : ℕ) (hL : PairCodegreeBound R L) :
    ∃p∈validWindowPaths G m x y W Z B,
      ((∑k:Fin (m+1),rootedCount
        (insert {e v,e (p.getVert k.val),e (p.getVert (k.val+1))} R)
        {e v,e (p.getVert k.val),e (p.getVert (k.val+1))}):ℝ)  ≤ 
      ((Fintype.card A:ℝ)/W.card)*(((m+1:ℕ):ℝ)*(L:ℝ)^3)/(a/(2:ℝ)^(m+3)) := by
  have hDense := dense_validWindowPaths G W a q m x y ha hq hm hOrder hWindow hPaths Z B b hZ hB hb
  let κ:ℝ := a/(2:ℝ)^(m+3)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hnV : 0 < (Fintype.card V:ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨v⟩ : 0 < Fintype.card V)
  have hW : 0 < (W.card:ℝ) := (by positivity : 0 < q*Fintype.card V/4).trans_le hWindowLower
  have hPower : (W.card:ℝ)^m ≤ (2*q*Fintype.card V)^m :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hWindow m
  have hIdentity : κ*(2*q*Fintype.card V)^m=a*(Fintype.card V:ℝ)^m*q^m/8 := by
    dsimp only [κ]
    rw [pow_add,mul_pow,mul_pow]
    norm_num
    field_simp
  have hCount : κ*(W.card:ℝ)^m ≤ (validWindowPaths G m x y W Z B).card := by
    calc
      _  ≤  κ*(2*q*Fintype.card V)^m := mul_le_mul_of_nonneg_left hPower hκ.le
      _ = a*(Fintype.card V:ℝ)^m*q^m/8 := hIdentity
      _  ≤  _ := hDense
  exact exists_low_cost_ambient_relative_window_path e G m hm v x y W Z B R L hL κ hκ hW hCount

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.fanPathCoordinates_map
#print axioms TypedTriangle.Pasch.exists_low_cost_ambient_relative_window_path

#print axioms TypedTriangle.Pasch.exists_low_cost_ambient_relative_dense_window_path
