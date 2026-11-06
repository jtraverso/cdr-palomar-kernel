module
public import RequestProject.TypedTriangle.PaschEdgeSelection
public import RequestProject.TypedTriangle.PaschEmbedding
public import RequestProject.TypedTriangle.PaschProtectedChildExceptions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace TypedTriangle.Pasch
variable {X V : Type*} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

/-- Restricting the free coordinate to an embedded child does not change
the ambient completion bound. In particular the right side is |V|, not |X|. -/
theorem sum_rooted_completions_embedded_le (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (a b : V) (hab : a ≠ b) :
    (∑ x : X, rootedCount (insert {a,b,e x} R) {a,b,e x}) ≤ Fintype.card V*L^3 := by
  calc
    _ = ∑ c ∈ (univ : Finset X).map e, rootedCount (insert {a,b,c} R) {a,b,c} := by
      rw [sum_map]
    _ ≤ ∑ c : V, rootedCount (insert {a,b,c} R) {a,b,c} :=
      sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := sum_rooted_completions_le R L hL a b hab

/-- The candidate pool is a subset of the child. The root endpoints and
previous universe remain ambient, with the necessary factor |V|/|X| retained. -/
theorem exists_rooted_completion_in_embedded_child (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (a b : V) (hab : a ≠ b) (W : Finset X) (κ : ℝ) (hκ : 0 < κ)
    (hnX : 0 < (Fintype.card X : ℝ)) (hW : κ*(Fintype.card X : ℝ) ≤ W.card) :
    ∃ x ∈ W, (rootedCount (insert {a,b,e x} R) {a,b,e x} : ℝ) ≤
      ((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ := by
  have hPos : 0 < (W.card : ℝ) := (mul_pos hκ hnX).trans_le hW
  obtain ⟨x0,hx0⟩ := card_pos.mp (by exact_mod_cast hPos : 0 < W.card)
  have hMap : (W.map e).Nonempty := ⟨e x0,mem_map.mpr ⟨x0,hx0,rfl⟩⟩
  obtain ⟨c,hc,hAvg⟩ := exists_rooted_completion_average R L hL a b hab (W.map e) hMap
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hc
  rw [card_map] at hAvg
  have hAvgR : (W.card : ℝ)*(rootedCount (insert {a,b,e x} R) {a,b,e x} : ℝ) ≤
      (Fintype.card V : ℝ)*(L : ℝ)^3 := by exact_mod_cast hAvg
  have hScaled := (mul_le_mul_of_nonneg_right hW
    (Nat.cast_nonneg (rootedCount (insert {a,b,e x} R) {a,b,e x}))).trans hAvgR
  have hBound : (rootedCount (insert {a,b,e x} R) {a,b,e x} : ℝ) ≤
      ((Fintype.card V : ℝ)*(L : ℝ)^3)/(κ*Fintype.card X) := by
    apply (le_div_iff₀ (mul_pos hκ hnX)).mpr
    convert hScaled using 1 <;> ring
  have hEq : ((Fintype.card V : ℝ)*(L : ℝ)^3)/(κ*Fintype.card X) =
      ((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ := by
    field_simp [ne_of_gt hκ,ne_of_gt hnX] <;> ring
  exact ⟨x,hx,hEq ▸ hBound⟩

/-- A quadratic number of choices in the child incurs a cost linear in
ambient order times child order. No replacement of |V| by |X| is made. -/
theorem embedded_quadratic_cost_le_linear (m L : ℕ) (κ δ : ℝ)
    (hκ : 0 < κ) (hnX : 0 < (Fintype.card X : ℝ))
    (hM : (m : ℝ) ≤ δ*(Fintype.card X : ℝ)^2) :
    (m : ℝ)*((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ ≤
      δ*(L : ℝ)^3/κ*Fintype.card V*Fintype.card X := by
  have hFactor : 0 ≤ ((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ := by positivity
  calc
    _ = (m : ℝ)*(((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ) := by ring
    _ ≤ (δ*(Fintype.card X : ℝ)^2)*
        (((Fintype.card V : ℝ)/Fintype.card X)*(L : ℝ)^3/κ) :=
      mul_le_mul_of_nonneg_right hM hFactor
    _ = _ := by field_simp [ne_of_gt hκ,ne_of_gt hnX] <;> ring

/-- Two or more genuinely new child blocks force each old block of the
Pasch into the actual exception family. Its size is bounded by the existing
childExceptions_card_le_holes, without protecting every internal child edge. -/
theorem old_block_mem_embedded_childExceptions (e : X ↪ V)
    {K : Finset (Finset V)} (hK : IsPasch K)
    (New : Finset (Finset X)) (hNew : mapConfiguration e New ⊆ K) (hTwo : 2 ≤ New.card)
    (P : Finset (Finset V)) {T : Finset V} (hTP : T ∈ P) (hTK : T ∈ K)
    (hOld : T ∉ mapConfiguration e New) :
    T ∈ childExceptions P ((univ : Finset X).map e) := by
  have hTwoMap : 2 ≤ (mapConfiguration e New).card := by
    simpa only [mapConfiguration,card_map] using hTwo
  have hInside : ∀ Q ∈ mapConfiguration e New, Q ⊆ (univ : Finset X).map e := by
    intro Q hQ
    obtain ⟨A,hA,rfl⟩ := mem_mapConfiguration.mp hQ
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
    exact mem_map.mpr ⟨x,mem_univ _,rfl⟩
  exact mem_filter.mpr ⟨hTP,old_block_exceptional_of_new_family hK
    ((univ : Finset X).map e) (mapConfiguration e New) hNew hTwoMap hInside hTK hOld⟩

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.sum_rooted_completions_embedded_le
#print axioms TypedTriangle.Pasch.exists_rooted_completion_in_embedded_child
#print axioms TypedTriangle.Pasch.embedded_quadratic_cost_le_linear
#print axioms TypedTriangle.Pasch.old_block_mem_embedded_childExceptions
