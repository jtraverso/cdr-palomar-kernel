module
public import RequestProject.TypedTriangle.PaschAmbientChildSupport
public import RequestProject.TypedTriangle.PaschFreeCoordinateAveraging
public import RequestProject.TypedTriangle.SeedPositivity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

def ambientRootedWeight (R : Finset (Finset V)) (L : ℕ) (Q : Finset V) : ℝ :=
  (rootedCount (insert Q R) Q : ℝ)/((Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3)

theorem ambient_completion_count_le (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (Q : Finset V) :
    rootedCount (insert Q R) Q ≤ Fintype.card V*L^3 := by
  by_cases hQ : Q.card = 3
  · obtain ⟨a,b,c,_,_,_,rfl⟩ := card_eq_three.mp hQ
    have hSingle : rootedCount (insert {a,b,c} R) {a,b,c} ≤
        ∑ z : V, rootedCount (insert {a,b,z} R) {a,b,z} :=
      single_le_sum (f := fun z : V => rootedCount (insert {a,b,z} R) {a,b,z})
        (fun _ _ => Nat.zero_le _) (mem_univ c)
    exact hSingle.trans (sum_rooted_completions_le_any R L hL a b)
  · have hz : rootedCount (insert Q R) Q = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro K hK
      obtain ⟨hConf,hQK⟩ := mem_filter.mp hK
      exact hQ ((mem_configurations.mp hConf).2.2.2.1 Q hQK)
    rw [hz]
    exact Nat.zero_le _

theorem ambientRootedWeight_bounds (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (hn : 0 < (Fintype.card V : ℝ)) (Q : Finset V) :
    0 ≤ ambientRootedWeight R L Q ∧ ambientRootedWeight R L Q ≤ 1 := by
  have hM : 0 < (Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3 := by positivity
  have hCount : (rootedCount (insert Q R) Q : ℝ) ≤
      (Fintype.card V : ℝ)*(L : ℝ)^3 := by exact_mod_cast ambient_completion_count_le R L hL Q
  have hPower : (L : ℝ)^3 ≤ ((L+1 : ℕ) : ℝ)^3 := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ L) 3
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hM.le
  · apply (div_le_iff₀ hM).mpr
    simpa only [one_mul] using hCount.trans
      (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg (Fintype.card V)))

section Child
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- All child triples are covered by ordered triples of child vertices.
The free-coordinate completion bound keeps the ambient order |V|. -/
theorem sum_child_triples_rooted_le (e : X ↪ V) (R : Finset (Finset V))
    (L : ℕ) (hL : PairCodegreeBound R L) :
    (∑ Q ∈ (univ : Finset X).powersetCard 3,
      (rootedCount (insert (Q.map e) R) (Q.map e) : ℝ)) ≤
        (Fintype.card X : ℝ)^2*Fintype.card V*(L : ℝ)^3 := by
  let F : Finset X → ℝ := fun Q => (rootedCount (insert (Q.map e) R) (Q.map e) : ℝ)
  let C : X → X → Finset (Finset X) := fun a b =>
    (univ : Finset X).biUnion (fun c => {{a,b,c}})
  let B : X → Finset (Finset X) := fun a => (univ : Finset X).biUnion (C a)
  let U : Finset (Finset X) := (univ : Finset X).biUnion B
  have hF : ∀ Q, 0 ≤ F Q := fun _ => Nat.cast_nonneg _
  have hCover : (univ : Finset X).powersetCard 3 ⊆ U := by
    intro Q hQ
    have hQc := (mem_powersetCard.mp hQ).2
    obtain ⟨a,b,c,_,_,_,rfl⟩ := card_eq_three.mp hQc
    exact mem_biUnion.mpr ⟨a,mem_univ _,mem_biUnion.mpr
      ⟨b,mem_univ _,mem_biUnion.mpr ⟨c,mem_univ _,mem_singleton_self _⟩⟩⟩
  have hThird : ∀ a b : X, (∑ c : X, F {a,b,c}) ≤
      (Fintype.card V : ℝ)*(L : ℝ)^3 := by
    intro a b
    have hNat : (∑ c : X, rootedCount (insert {e a,e b,e c} R) {e a,e b,e c}) ≤
        Fintype.card V*L^3 := by
      calc
        _ = ∑ c ∈ (univ : Finset X).map e,
            rootedCount (insert {e a,e b,c} R) {e a,e b,c} := by rw [sum_map]
        _ ≤ ∑ c : V, rootedCount (insert {e a,e b,c} R) {e a,e b,c} :=
          sum_le_sum_of_subset (subset_univ _)
        _ ≤ _ := sum_rooted_completions_le_any R L hL (e a) (e b)
    dsimp only [F]
    simp only [map_insert,map_singleton]
    exact_mod_cast hNat
  change (∑ Q ∈ (univ : Finset X).powersetCard 3, F Q) ≤ _
  calc
    _ ≤ ∑ Q ∈ U, F Q := sum_le_sum_of_subset_of_nonneg hCover (fun _ _ _ => hF _)
    _ ≤ ∑ a : X, ∑ Q ∈ B a, F Q := sum_biUnion_le_of_nonneg _ _ _ hF
    _ ≤ ∑ a : X, ∑ b : X, ∑ Q ∈ C a b, F Q :=
      sum_le_sum (fun a _ => sum_biUnion_le_of_nonneg _ _ _ hF)
    _ ≤ ∑ a : X, ∑ b : X, ∑ c : X, F {a,b,c} := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      have hh := sum_biUnion_le_of_nonneg (univ : Finset X)
        (fun c => ({{a,b,c}} : Finset (Finset X))) F hF
      simpa only [sum_singleton] using hh
    _ ≤ ∑ _a : X, ∑ _b : X, (Fintype.card V : ℝ)*(L : ℝ)^3 :=
      sum_le_sum (fun a _ => sum_le_sum (fun b _ => hThird a b))
    _ = _ := by simp [pow_two,mul_comm,mul_left_comm,mul_assoc]

theorem sum_child_triples_ambientRootedWeight_le (e : X ↪ V)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (hn : 0 < (Fintype.card V : ℝ)) :
    (∑ Q ∈ (univ : Finset X).powersetCard 3, ambientRootedWeight R L (Q.map e)) ≤
      (Fintype.card X : ℝ)^2 := by
  have hM : 0 < (Fintype.card V : ℝ)*((L+1 : ℕ) : ℝ)^3 := by positivity
  simp only [ambientRootedWeight]
  rw [←sum_div]
  apply (div_le_iff₀ hM).mpr
  have hPower : (L : ℝ)^3 ≤ ((L+1 : ℕ) : ℝ)^3 := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ L) 3
  calc
    _ ≤ (Fintype.card X : ℝ)^2*Fintype.card V*(L : ℝ)^3 :=
      sum_child_triples_rooted_le e R L hL
    _ ≤ (Fintype.card X : ℝ)^2*Fintype.card V*((L+1 : ℕ) : ℝ)^3 :=
      mul_le_mul_of_nonneg_left hPower (by positivity)
    _ = _ := by ring

end Child
end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.ambient_completion_count_le
#print axioms TypedTriangle.Pasch.ambientRootedWeight_bounds
#print axioms TypedTriangle.Pasch.sum_child_triples_rooted_le
#print axioms TypedTriangle.Pasch.sum_child_triples_ambientRootedWeight_le
