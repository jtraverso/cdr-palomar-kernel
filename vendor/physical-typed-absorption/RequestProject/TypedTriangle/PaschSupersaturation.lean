module
public import RequestProject.TypedTriangle.PaschEmbedding
public import RequestProject.TypedTriangle.PaschBoxIndicator
public import RequestProject.TypedTriangle.PaschSixTupleCollisions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def injectiveBox (H : Host V I) (F : Set (Multiset I)) : Finset (Fin 6 → V) :=
  univ.filter (fun f => boxAllowed H F f ∧ Function.Injective f)

theorem gridImage_subset_allowed {H : Host V I} {F : Set (Multiset I)}
    {f : Fin 6 → V} (hf : boxAllowed H F f) : gridImage f ⊆ allowed H F := by
  intro T hT
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
  have hA' : A = {0,2,4} ∨ A = {0,3,5} ∨ A = {1,2,5} ∨ A = {1,3,4} := by
    simpa only [gridPasch,mem_insert,mem_singleton] using hA
  rcases hA' with rfl | rfl | rfl | rfl
  · exact mem_filter.mpr ⟨mem_univ _,by simpa [image_insert,image_singleton] using hf 0 0 0⟩
  · exact mem_filter.mpr ⟨mem_univ _,by simpa [image_insert,image_singleton] using hf 0 1 1⟩
  · exact mem_filter.mpr ⟨mem_univ _,by simpa [image_insert,image_singleton] using hf 1 0 1⟩
  · exact mem_filter.mpr ⟨mem_univ _,by simpa [image_insert,image_singleton] using hf 1 1 0⟩

theorem injectiveBox_maps_to_configurations (H : Host V I) (F : Set (Multiset I)) :
    ∀ f ∈ injectiveBox H F, gridImage f ∈ configurations (allowed H F) := by
  intro f hf
  obtain ⟨hBox,hInj⟩ := (mem_filter.mp hf).2
  have hP := gridImage_isPasch f hInj
  exact mem_configurations.mpr ⟨gridImage_subset_allowed hBox,hP.1,hP⟩

/-- The fibers are bounded on actual unoriented configurations, rather
than treating different six-tuples as different Pasch copies. -/
theorem injectiveBox_card_le (H : Host V I) (F : Set (Multiset I)) :
    (injectiveBox H F).card ≤ 6^6 * count (allowed H F) := by
  have hmap := injectiveBox_maps_to_configurations H F
  have hcard : (injectiveBox H F).card = ∑ S ∈ configurations (allowed H F),
      ((injectiveBox H F).filter (fun f => gridImage f = S)).card := by
    have hs := sum_fiberwise_of_maps_to hmap (fun _ => (1:ℕ))
    simpa only [sum_const,Nat.nsmul_eq_mul,Nat.mul_one] using hs.symm
  rw [hcard]
  calc
    (∑ S ∈ configurations (allowed H F), ((injectiveBox H F).filter (fun f => gridImage f = S)).card)
      ≤ ∑ _S ∈ configurations (allowed H F), (6^6:ℕ) := by
        apply sum_le_sum
        intro S hS
        have hSub : (injectiveBox H F).filter (fun f => gridImage f = S) ⊆
            univ.filter (fun f : Fin 6 → V => Function.Injective f ∧ gridImage f = S) := by
          intro f hf
          obtain ⟨hf,hEq⟩ := mem_filter.mp hf
          exact mem_filter.mpr ⟨mem_univ _,⟨(mem_filter.mp hf).2.2,hEq⟩⟩
        exact (card_le_card hSub).trans (gridImage_fiber_card_le S
          (mem_configurations.mp hS).2.2.2.2.1)
    _ = _ := by simp [count,Nat.mul_comm]

theorem boxAllowed_card_le_good_and_collisions (H : Host V I) (F : Set (Multiset I)) :
    (univ.filter (boxAllowed H F)).card ≤ (injectiveBox H F).card + 15*(Fintype.card V)^5 := by
  let B := univ.filter (fun f : Fin 6 → V => ¬ Function.Injective f)
  have hSub : univ.filter (boxAllowed H F) ⊆ injectiveBox H F ∪ B := by
    intro f hf
    by_cases hInj : Function.Injective f
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hf).2,hInj⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hInj⟩)
  exact (card_le_card hSub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left sixTupleCollisions_card_le _))

def supersaturationOrder (α : ℝ) : ℕ := max 6 ⌈30/α^24⌉₊

def massConstant (α C : ℝ) : ℝ := α^24/(2*6^6*C^4)

/-- An allowed root and H3 force quadratically many fractional Pasches.
The nonempty branch is explicit; an empty host has zero target instead. -/
theorem count_lower_of_common_neighbors {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 < α)
    (hN : supersaturationOrder α ≤ Fintype.card V)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    α^24*(Fintype.card V : ℝ)^6/(2*6^6) ≤ (count (allowed H F) : ℝ) := by
  let n := (Fintype.card V : ℝ)
  have hnNat : 0 < Fintype.card V := by
    have hs : 6 ≤ Fintype.card V := (le_max_left _ _).trans hN
    omega
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast hnNat
  have hNreal : 30/α^24 ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have hscale : 30 ≤ n*α^24 := (div_le_iff₀ (pow_pos hα 24)).mp hNreal
  have hbad : 15*n^5 ≤ α^24*n^6/2 := by
    have hs : (15:ℝ) ≤ α^24*n/2 := by nlinarith only [hscale]
    have hp := mul_le_mul_of_nonneg_right hs (pow_nonneg hn.le 5)
    convert hp using 1 <;> ring
  have hBox := boxAllowed_card_lower hH3 hα.le hnNat hT
  have hUp : ((univ.filter (boxAllowed H F)).card : ℝ) ≤
      (injectiveBox H F).card + 15*n^5 := by
    dsimp only [n]
    exact_mod_cast boxAllowed_card_le_good_and_collisions H F
  have hGood : α^24*n^6/2 ≤ ((injectiveBox H F).card : ℝ) := by
    change α^24*n^6 ≤ _ at hBox
    linarith only [hBox,hUp,hbad]
  have hFiber : ((injectiveBox H F).card : ℝ) ≤ (6:ℝ)^6*count (allowed H F) := by
    exact_mod_cast injectiveBox_card_le H F
  have ht := hGood.trans hFiber
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2*6^6)).mpr
  nlinarith only [ht]

theorem target_lower_of_seed_and_common_neighbors {H : Host V I} {F : Set (Multiset I)}
    {α C : ℝ} {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 0 < C)
    (hN : supersaturationOrder α ≤ Fintype.card V)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    massConstant α C * (Fintype.card V : ℝ)^2 ≤ target μ (allowed H F) := by
  let n := (Fintype.card V : ℝ)
  have hnNat : 0 < Fintype.card V := by
    have hs : 6 ≤ Fintype.card V := (le_max_left _ _).trans hN
    omega
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast hnNat
  have hc := count_lower_of_common_neighbors hH3 hα hN hT
  have hbase : 0 ≤ 1/(C*n) := by positivity
  have hterm : ∀ S ∈ configurations (allowed H F), (1/(C*n))^4 ≤ ∏ T ∈ S, μ T := by
    intro S hS
    obtain ⟨hSub,hCard,hPasch⟩ := mem_configurations.mp hS
    calc
      (1/(C*n))^4 = ∏ _T ∈ S, 1/(C*n) := by simp [hCard]
      _ ≤ _ := prod_le_prod₀ (fun _ _ => hbase)
        (fun T hT => (hH1.1 T ((mem_filter.mp (hSub hT)).2)).1)
  have hm : (1/(C*n))^4 * count (allowed H F) ≤ target μ (allowed H F) := by
    rw [target,statistic_eq_sum]
    calc
      _ = ∑ _S ∈ configurations (allowed H F), (1/(C*n))^4 := by simp [count,mul_comm]
      _ ≤ _ := sum_le_sum hterm
  have hcp := mul_le_mul_of_nonneg_left hc (pow_nonneg hbase 4)
  have heq : (1/(C*n))^4 * (α^24*n^6/(2*6^6)) = massConstant α C * n^2 := by
    unfold massConstant
    field_simp [ne_of_gt hC,ne_of_gt hn]
    <;> ring
  change (1/(C*n))^4 * (α^24*n^6/(2*6^6)) ≤ _ at hcp
  rw [heq] at hcp
  exact hcp.trans hm

#print axioms gridImage_subset_allowed
#print axioms injectiveBox_card_le
#print axioms boxAllowed_card_le_good_and_collisions
#print axioms count_lower_of_common_neighbors
#print axioms target_lower_of_seed_and_common_neighbors
end TypedTriangle.Pasch
