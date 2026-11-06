module
public import RequestProject.TypedTriangle.PaschAmbientRootedMonitor
public import RequestProject.TypedTriangle.PaschRawProfileBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {X V I : Type*} [Fintype X] [Fintype V]

theorem exists_allowed_root_of_positive_load {H : Host X I} {F : Set (Multiset I)}
    {μ : Finset X → ℝ} (hLoad : ∀ f ∈ edges H, 0 < bdry H F μ f)
    (hE : (edges H).Nonempty) : ∃ a b c : X, IsAllowed H F {a,b,c} := by
  have hA : (allowed H F).Nonempty := by
    obtain ⟨f,hf⟩ := hE
    by_contra hEmpty
    have hz : allowed H F = ∅ := not_nonempty_iff_eq_empty.mp hEmpty
    have hh := hLoad f hf
    rw [bdry_eq_sum_triOn] at hh
    simp only [triOn,hz,filter_empty,sum_empty] at hh
    exact lt_irrefl _ hh
  obtain ⟨T,hT⟩ := hA
  have hAllow := isAllowed_of_mem_allowed hT
  obtain ⟨a,b,c,_,_,_,hSet⟩ := card_eq_three.mp hAllow.1
  exact ⟨a,b,c,by simpa only [hSet] using hAllow⟩

private theorem root_order_pos (e : X ↪ V) (hn : 0 < (Fintype.card X:ℝ)) :
    0 < (Fintype.card V:ℝ) := by
  have hX : 0 < Fintype.card X := by exact_mod_cast hn
  exact_mod_cast lt_of_lt_of_le hX (Fintype.card_le_of_injective e e.injective)

private theorem padded_target_identity (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (H : Host X I) (F : Set (Multiset I)) (μ : Finset X → ℝ) :
    (∑ Q ∈ allowed H F, μ Q*childPaddedWeight e R L Q) =
      ((∑ Q ∈ allowed H F, μ Q*ambientRootedWeight R L (Q.map e))+
       (∑ Q ∈ allowed H F, μ Q*(1/Fintype.card X)))/2 := by
  simp only [childPaddedWeight,mul_div,mul_add]
  rw [←sum_div,sum_add_distrib]

/-- Coefficient upper bounds suffice for the linear ambient mass bound;
no unit-load identity or exact seed is required. -/
theorem raw_child_padded_target_upper (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) {H : Host X I} {F : Set (Multiset I)}
    {b : ℝ} {μ : Finset X → ℝ} (hb : 0 ≤ b) (hn : 0 < (Fintype.card X:ℝ))
    (hμ : ∀ T, IsAllowed H F T → 0 ≤ μ T ∧ μ T ≤ b/Fintype.card X) :
    (∑ Q ∈ allowed H F, μ Q*childPaddedWeight e R L Q) ≤ b*Fintype.card X := by
  let n := (Fintype.card X:ℝ)
  have hV := root_order_pos e hn
  have hw (Q : Finset X) : 0 ≤ ambientRootedWeight R L (Q.map e) :=
    (ambientRootedWeight_bounds R L hL hV (Q.map e)).1
  have hSub : allowed H F ⊆ (univ : Finset X).powersetCard 3 := by
    intro Q hQ
    exact mem_powersetCard.mpr ⟨subset_univ _,(isAllowed_of_mem_allowed hQ).1⟩
  have hWeightSum : (∑ Q ∈ allowed H F, ambientRootedWeight R L (Q.map e)) ≤ n^2 :=
    (sum_le_sum_of_subset_of_nonneg hSub (fun Q _ _ => hw Q)).trans
      (sum_child_triples_ambientRootedWeight_le e R L hL hV)
  have hAmbient : (∑ Q ∈ allowed H F, μ Q*ambientRootedWeight R L (Q.map e)) ≤ b*n := by
    calc
      _ ≤ ∑ Q ∈ allowed H F, (b/n)*ambientRootedWeight R L (Q.map e) :=
        sum_le_sum (fun Q hQ => mul_le_mul_of_nonneg_right
          (hμ Q (isAllowed_of_mem_allowed hQ)).2 (hw Q))
      _ = (b/n)*∑ Q ∈ allowed H F, ambientRootedWeight R L (Q.map e) := by rw [mul_sum]
      _ ≤ (b/n)*n^2 := mul_le_mul_of_nonneg_left hWeightSum (div_nonneg hb hn.le)
      _ = _ := by field_simp [ne_of_gt hn] <;> ring
  have hCard : ((allowed H F).card:ℝ) ≤ n^3 := by
    dsimp only [n]
    exact_mod_cast card_allowed_le H F
  have hMass : (∑ Q ∈ allowed H F, μ Q) ≤ b*n^2 := by
    calc
      _ ≤ ∑ _Q ∈ allowed H F, b/n :=
        sum_le_sum (fun Q hQ => (hμ Q (isAllowed_of_mem_allowed hQ)).2)
      _ = ((allowed H F).card:ℝ)*(b/n) := by simp
      _ ≤ n^3*(b/n) := mul_le_mul_of_nonneg_right hCard (div_nonneg hb hn.le)
      _ = _ := by field_simp [ne_of_gt hn] <;> ring
  have hBase : (∑ Q ∈ allowed H F, μ Q*(1/Fintype.card X)) ≤ b*n := by
    calc
      _ = (∑ Q ∈ allowed H F, μ Q)/n := by simp only [n,div_eq_mul_inv,one_mul,sum_mul]
      _ ≤ _ := (div_le_iff₀ hn).mpr (by simpa only [pow_two,mul_assoc] using hMass)
  rw [padded_target_identity]
  linarith only [hAmbient,hBase]

/-- The quota for the padded ambient monitor follows from a positive raw
load and the literal coefficient lower window, with no exact H1. -/
theorem raw_child_padded_target_lower_or_empty (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) {H : Host X I} {F : Set (Multiset I)}
    {a α : ℝ} {μ : Finset X → ℝ} (ha : 0 < a) (hα : 0 < α)
    (hn : 0 < (Fintype.card X:ℝ))
    (hLow : ∀ T, IsAllowed H F T → a/Fintype.card X ≤ μ T)
    (hLoad : ∀ f ∈ edges H, 0 < bdry H F μ f) (h3 : CommonNbrCond H F α) :
    (edges H = ∅ ∧ (∑ Q ∈ allowed H F, μ Q*childPaddedWeight e R L Q) = 0) ∨
      (a*α^3/54)*Fintype.card X ≤ ∑ Q ∈ allowed H F, μ Q*childPaddedWeight e R L Q := by
  by_cases hE : edges H = ∅
  · exact Or.inl ⟨hE,by simp only [allowed_empty_of_edges_empty hE,sum_empty]⟩
  obtain ⟨x,y,z,hT⟩ := exists_allowed_root_of_positive_load hLoad (nonempty_iff_ne_empty.mpr hE)
  have hDensity := allowed_density_of_triangle h3 hα.le hT
  have hEach : ((allowed H F).card:ℝ)*(a/Fintype.card X)*(1/Fintype.card X) ≤
      ∑ Q ∈ allowed H F, μ Q*(1/Fintype.card X) := by
    calc
      _ = ∑ _Q ∈ allowed H F, (a/Fintype.card X)*(1/Fintype.card X) := by simp [mul_assoc]
      _ ≤ _ := sum_le_sum (fun Q hQ => mul_le_mul_of_nonneg_right
        (hLow Q (isAllowed_of_mem_allowed hQ)) (by positivity))
  have hBase : (a*α^3/27)*Fintype.card X ≤ ∑ Q ∈ allowed H F, μ Q*(1/Fintype.card X) := by
    calc
      _ = ((α*(Fintype.card X:ℝ))^3/27)*(a/Fintype.card X)*(1/Fintype.card X) := by
        field_simp [ne_of_gt hn] <;> ring
      _ ≤ ((allowed H F).card:ℝ)*(a/Fintype.card X)*(1/Fintype.card X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDensity (by positivity)) (by positivity)
      _ ≤ _ := hEach
  have hV := root_order_pos e hn
  have hAmbient0 : 0 ≤ ∑ Q ∈ allowed H F, μ Q*ambientRootedWeight R L (Q.map e) := by
    apply sum_nonneg
    intro Q hQ
    exact mul_nonneg ((by positivity : (0:ℝ) ≤ a/Fintype.card X).trans
      (hLow Q (isAllowed_of_mem_allowed hQ)))
      (ambientRootedWeight_bounds R L hL hV (Q.map e)).1
  apply Or.inr
  rw [padded_target_identity]
  linarith only [hBase,hAmbient0]

#print axioms exists_allowed_root_of_positive_load
#print axioms raw_child_padded_target_upper
#print axioms raw_child_padded_target_lower_or_empty
end TypedTriangle.Pasch
