module
public import RequestProject.TypedTriangle.PaschWeightedWindowPaths
public import RequestProject.TypedTriangle.PaschAmbientSupportPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical S07V24
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An exact re-encoding of a supported assignment family in the window
subtype. Projection recovers the original assignment; no second sample is used. -/
def restrictedAssignments {m : ℕ} (P : Finset (Fin m → V)) (W : Finset V)
    (hSupp : ∀ f ∈ P, ∀ i : Fin m, f i ∈ W) : Finset (Fin m → W) :=
  P.attach.image (fun (f : ↥P) (i : Fin m) => (⟨f.val i,hSupp f.val f.property i⟩ : W))

theorem restrictedAssignments_card {m : ℕ} (P : Finset (Fin m → V)) (W : Finset V)
    (hSupp : ∀ f ∈ P, ∀ i : Fin m, f i ∈ W) :
    (restrictedAssignments P W hSupp).card = P.card := by
  unfold restrictedAssignments
  calc
    _ = P.attach.card := card_image_of_injOn (by
      intro f hf g hg hfg
      apply Subtype.ext
      funext i
      exact congrArg (fun u : Fin m → W => (u i).val) hfg)
    _ = _ := card_attach

theorem restrictedAssignments_project {m : ℕ} (P : Finset (Fin m → V)) (W : Finset V)
    (hSupp : ∀ f ∈ P, ∀ i : Fin m, f i ∈ W)
    {g : Fin m → W} (hg : g ∈ restrictedAssignments P W hSupp) :
    (fun i => (g i).val) ∈ P := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hg
  exact f.property

theorem windowPathAssignments_supported (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (x y : V) (W Z : Finset V) (B : SimpleGraph V) :
    ∀ f ∈ windowPathAssignments G m x y W Z B, ∀ i : Fin m, f i ∈ W := by
  intro f hf i
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hf
  have hPaths := (mem_filter.mp hp).1
  have hInside := (mem_filter.mp hPaths).2
  exact hInside ((mem_intlSet m p (intl m p i)).mpr ⟨i,rfl⟩)

/-- Relative density is measured in W^m, while the previous universe and
both root endpoints remain ambient. The cost retains |V|/|W| exactly. -/
theorem exists_low_cost_relative_window_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 0 < m) (v x y : V) (W Z : Finset V) (B : SimpleGraph V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (κ : ℝ) (hκ : 0 < κ) (hW : 0 < (W.card : ℝ))
    (hCount : κ*(W.card : ℝ)^m ≤ (validWindowPaths G m x y W Z B).card) :
    ∃ p ∈ validWindowPaths G m x y W Z B,
      ((∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)}) : ℝ) ≤
          ((Fintype.card V : ℝ)/W.card)*(((m+1 : ℕ) : ℝ)*(L : ℝ)^3)/κ := by
  let P := windowPathAssignments G m x y W Z B
  have hSupp : ∀ f ∈ P, ∀ i : Fin m, f i ∈ W := windowPathAssignments_supported G m x y W Z B
  let PW := restrictedAssignments P W hSupp
  let e : W ↪ V := Function.Embedding.subtype (fun z => z ∈ W)
  have hDensity : κ*(Fintype.card (Fin m → W) : ℝ) ≤ PW.card := by
    simpa only [PW,restrictedAssignments_card,P,windowPathAssignments_card,
      Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow] using hCount
  choose i other hForm using (fun k : Fin (m+1) => fan_triangle_has_free_coordinate m hm v x y k)
  let otherW : ∀ k, ({j : Fin m // j ≠ i k} → W) → V :=
    fun k r => other k (fun j => (r j).val)
  have hnW : 0 < (Fintype.card W : ℝ) := by simpa only [Fintype.card_coe] using hW
  obtain ⟨g,hg,hCost⟩ := exists_low_embedded_support_potential e R L hL i (fun _ _ => v)
    otherW PW κ hκ hnW hDensity
  let f : Fin m → V := fun j => (g j).val
  have hf : f ∈ P := restrictedAssignments_project P W hSupp hg
  have hFan : embeddedSupportCompletionCost e R i (fun _ _ => v) otherW g =
      fanCompletionCost R v x y f := by
    unfold embeddedSupportCompletionCost fanCompletionCost
    apply sum_congr rfl
    intro k _
    have ht := congrArg (fun Q => rootedCount (insert Q R) Q) (hForm k f).symm
    change rootedCount (insert {v,other k (fun j => (g j.val).val),(g (i k)).val} R)
      {v,other k (fun j => (g j.val).val),(g (i k)).val} = _
    exact ht
  obtain ⟨p,hp,hCoordinates⟩ := windowPathAssignments_realize G m x y W Z B hf
  have hWalk : fanCompletionCost R v x y f = ∑ k : Fin (m+1), rootedCount
      (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
      {v,p.getVert k.val,p.getVert (k.val+1)} := by
    unfold fanCompletionCost
    apply sum_congr rfl
    intro k _
    have ht : fanTriangle v x y f k = {v,p.getVert k.val,p.getVert (k.val+1)} := by
      unfold fanTriangle fanPathCoordinates
      rw [hCoordinates]
      rfl
    rw [ht]
  exact ⟨p,hp,by simpa only [hFan,hWalk,Nat.cast_sum,Fintype.card_coe,Fintype.card_fin] using hCost⟩

/-- The same retained paths have positive relative density independent of q.
The lower window bound then makes the cost O(1/q), rather than O(q^(-m)). -/
theorem exists_low_cost_relative_dense_window_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (a q : ℝ) (m : ℕ) (v x y : V)
    (ha : 0 < a) (hq : 0 < q) (hm : 0 < m)
    (hOrder : 2 ≤ q*Fintype.card V)
    (hWindow : (W.card : ℝ) ≤ 2*q*Fintype.card V)
    (hWindowLower : q*Fintype.card V/4 ≤ (W.card : ℝ))
    (hPaths : a*(Fintype.card V : ℝ)^m*q^m/4 ≤ (pathsIn G m x y W).card)
    (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (b : ℕ)
    (hZ : (Z.card : ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (hB : ∀ z, B.degree z ≤ b) (hb : (b : ℝ) ≤ Vortex.windowRouteRate a q m*Fintype.card V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L) :
    ∃ p ∈ validWindowPaths G m x y W Z B,
      ((∑ k : Fin (m+1), rootedCount
        (insert {v,p.getVert k.val,p.getVert (k.val+1)} R)
        {v,p.getVert k.val,p.getVert (k.val+1)}) : ℝ) ≤
          4*(((m+1 : ℕ) : ℝ)*(L : ℝ)^3)/((a/(2 : ℝ)^(m+3))*q) := by
  have hDense := dense_validWindowPaths G W a q m x y ha hq hm hOrder hWindow hPaths Z B b hZ hB hb
  let κ : ℝ := a/(2 : ℝ)^(m+3)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hnV : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨v⟩ : 0 < Fintype.card V)
  have hW : 0 < (W.card : ℝ) := (by positivity : 0 < q*Fintype.card V/4).trans_le hWindowLower
  have hPower : (W.card : ℝ)^m ≤ (2*q*Fintype.card V)^m :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hWindow m
  have hIdentity : κ*(2*q*Fintype.card V)^m = a*(Fintype.card V : ℝ)^m*q^m/8 := by
    dsimp only [κ]
    rw [pow_add,mul_pow,mul_pow]
    norm_num
    field_simp
  have hCount : κ*(W.card : ℝ)^m ≤ (validWindowPaths G m x y W Z B).card := by
    calc
      _ ≤ κ*(2*q*Fintype.card V)^m := mul_le_mul_of_nonneg_left hPower hκ.le
      _ = a*(Fintype.card V : ℝ)^m*q^m/8 := hIdentity
      _ ≤ _ := hDense
  obtain ⟨p,hp,hCost⟩ := exists_low_cost_relative_window_path G m hm v x y W Z B R L hL κ hκ hW hCount
  have hRatio : (Fintype.card V : ℝ)/W.card ≤ 4/q :=
    (div_le_div_iff₀ hW hq).mpr (by nlinarith only [hWindowLower])
  refine ⟨p,hp,hCost.trans ?_⟩
  calc
    _ ≤ (4/q)*(((m+1 : ℕ) : ℝ)*(L : ℝ)^3)/κ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRatio (by positivity)) hκ.le
    _ = _ := by dsimp only [κ]; ring

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.restrictedAssignments_card
#print axioms TypedTriangle.Pasch.restrictedAssignments_project
#print axioms TypedTriangle.Pasch.windowPathAssignments_supported
#print axioms TypedTriangle.Pasch.exists_low_cost_relative_window_path
#print axioms TypedTriangle.Pasch.exists_low_cost_relative_dense_window_path
