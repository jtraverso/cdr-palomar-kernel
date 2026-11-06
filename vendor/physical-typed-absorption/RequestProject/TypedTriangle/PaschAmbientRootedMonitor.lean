module
public import RequestProject.TypedTriangle.PaschAmbientRootedMass
public import RequestProject.TypedTriangle.PaschHostDensity
public import RequestProject.TypedTriangle.PaschSupersaturationEndpoint
public import RequestProject.TypedTriangle.SeedMassScale
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

def childPaddedWeight (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (Q : Finset X) : ℝ := (ambientRootedWeight R L (Q.map e)+1/Fintype.card X)/2

private theorem ambient_order_pos (e : X ↪ V) (hn : 0 < (Fintype.card X : ℝ)) :
    0 < (Fintype.card V : ℝ) := by
  have hX : 0 < Fintype.card X := by exact_mod_cast hn
  have hCard := Fintype.card_le_of_injective e e.injective
  exact_mod_cast lt_of_lt_of_le hX hCard

theorem childPaddedWeight_bounds (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) (hn : 1 ≤ Fintype.card X) (Q : Finset X) :
    0 ≤ childPaddedWeight e R L Q ∧ childPaddedWeight e R L Q ≤ 1 := by
  have hn0 : (0 : ℝ) < Fintype.card X := by exact_mod_cast (by omega : 0 < Fintype.card X)
  have hn1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast hn
  have hV := ambient_order_pos e hn0
  obtain ⟨hw0,hw1⟩ := ambientRootedWeight_bounds R L hL hV (Q.map e)
  have hb0 : (0 : ℝ) ≤ 1/(Fintype.card X : ℝ) := by positivity
  have hb1 : 1/(Fintype.card X : ℝ) ≤ 1 :=
    (div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hn1)
  unfold childPaddedWeight
  constructor <;> linarith only [hw0,hw1,hb0,hb1]

theorem ambient_seed_target_upper (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) {H : Host X I} {F : Set (Multiset I)}
    {C : ℝ} {ψ : Finset X → ℝ} (hC : 0 < C) (hn : 0 < (Fintype.card X : ℝ))
    (hSeed : IsDiffuseSeed H F C ψ) :
    0 ≤ (∑ Q ∈ allowed H F, ψ Q*ambientRootedWeight R L (Q.map e)) ∧
      (∑ Q ∈ allowed H F, ψ Q*ambientRootedWeight R L (Q.map e)) ≤ C*Fintype.card X := by
  have hV := ambient_order_pos e hn
  have hw : ∀ Q : Finset X, 0 ≤ ambientRootedWeight R L (Q.map e) :=
    fun Q => (ambientRootedWeight_bounds R L hL hV (Q.map e)).1
  have hψ0 : ∀ Q ∈ allowed H F, 0 ≤ ψ Q := by
    intro Q hQ
    exact (by positivity : (0 : ℝ) ≤ 1/(C*Fintype.card X)).trans
      (hSeed.1 Q (isAllowed_of_mem_allowed hQ)).1
  have hSub : allowed H F ⊆ (univ : Finset X).powersetCard 3 := by
    intro Q hQ
    exact mem_powersetCard.mpr ⟨subset_univ _,(isAllowed_of_mem_allowed hQ).1⟩
  have hSum : (∑ Q ∈ allowed H F, ambientRootedWeight R L (Q.map e)) ≤
      (Fintype.card X : ℝ)^2 :=
    (sum_le_sum_of_subset_of_nonneg hSub (fun Q _ _ => hw Q)).trans
      (sum_child_triples_ambientRootedWeight_le e R L hL hV)
  constructor
  · exact sum_nonneg (fun Q hQ => mul_nonneg (hψ0 Q hQ) (hw Q))
  · calc
      _ ≤ ∑ Q ∈ allowed H F, (C/Fintype.card X)*ambientRootedWeight R L (Q.map e) := by
        apply sum_le_sum
        intro Q hQ
        exact mul_le_mul_of_nonneg_right
          (hSeed.1 Q (isAllowed_of_mem_allowed hQ)).2 (hw Q)
      _ = (C/Fintype.card X)*∑ Q ∈ allowed H F, ambientRootedWeight R L (Q.map e) := by rw [mul_sum]
      _ ≤ (C/Fintype.card X)*(Fintype.card X : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by field_simp [ne_of_gt hn] <;> ring

private theorem padded_target_identity (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (H : Host X I) (F : Set (Multiset I)) (ψ : Finset X → ℝ) :
    (∑ Q ∈ allowed H F, ψ Q*childPaddedWeight e R L Q) =
      ((∑ Q ∈ allowed H F, ψ Q*ambientRootedWeight R L (Q.map e))+
       (∑ Q ∈ allowed H F, ψ Q*(1/Fintype.card X)))/2 := by
  simp only [childPaddedWeight,mul_div,mul_add]
  rw [←sum_div,sum_add_distrib]

theorem child_padded_target_upper (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) {H : Host X I} {F : Set (Multiset I)}
    {C : ℝ} {ψ : Finset X → ℝ} (hC : 1 ≤ C) (hn : 0 < (Fintype.card X : ℝ))
    (hSeed : IsDiffuseSeed H F C ψ) :
    (∑ Q ∈ allowed H F, ψ Q*childPaddedWeight e R L Q) ≤ C*Fintype.card X := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hNorm := (ambient_seed_target_upper e R L hL hC0 hn hSeed).2
  have hMass := (LocalizedCover.seed_total_mass_cap hSeed).2
  have hBase : (∑ Q ∈ allowed H F, ψ Q*(1/Fintype.card X)) ≤ (Fintype.card X : ℝ) := by
    calc
      _ = (∑ Q ∈ allowed H F, ψ Q)/(Fintype.card X : ℝ) := by
        simp only [div_eq_mul_inv,one_div,sum_mul,one_mul]
      _ ≤ _ := (div_le_iff₀ hn).mpr (by simpa only [pow_two] using hMass)
  have hCM : (Fintype.card X : ℝ) ≤ C*Fintype.card X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (Fintype.card X))
  rw [padded_target_identity]
  linarith only [hNorm,hBase,hCM]

/-- The positive quota is derived from H1 and H3. If the child has no edges,
the actual target is zero and the packing branch must be empty. -/
theorem child_padded_target_lower_or_empty (e : X ↪ V) (R : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L) {H : Host X I} {F : Set (Multiset I)}
    {α C : ℝ} {ψ : Finset X → ℝ} (hα : 0 < α) (hC : 0 < C)
    (hn : 0 < (Fintype.card X : ℝ)) (hSeed : IsDiffuseSeed H F C ψ)
    (h3 : CommonNbrCond H F α) :
    (edges H = ∅ ∧ (∑ Q ∈ allowed H F, ψ Q*childPaddedWeight e R L Q) = 0) ∨
      α^3/(54*C)*Fintype.card X ≤ ∑ Q ∈ allowed H F, ψ Q*childPaddedWeight e R L Q := by
  by_cases hE : edges H = ∅
  · exact Or.inl ⟨hE,by simp only [allowed_empty_of_edges_empty hE,sum_empty]⟩
  obtain ⟨a,b,c,hT⟩ := exists_allowed_root_of_edges hSeed (nonempty_iff_ne_empty.mpr hE)
  have hDensity := allowed_density_of_triangle h3 hα.le hT
  have hEach : ((allowed H F).card : ℝ)*(1/(C*Fintype.card X))*(1/Fintype.card X) ≤
      ∑ Q ∈ allowed H F, ψ Q*(1/Fintype.card X) := by
    calc
      _ = ∑ _Q ∈ allowed H F, (1/(C*Fintype.card X))*(1/Fintype.card X) := by
        simp [mul_assoc]
      _ ≤ _ := sum_le_sum (fun Q hQ => mul_le_mul_of_nonneg_right
        (hSeed.1 Q (isAllowed_of_mem_allowed hQ)).1 (by positivity))
  have hBase : α^3/(27*C)*Fintype.card X ≤ ∑ Q ∈ allowed H F, ψ Q*(1/Fintype.card X) := by
    calc
      _ = ((α*(Fintype.card X : ℝ))^3/27)*(1/(C*Fintype.card X))*(1/Fintype.card X) := by
        field_simp [ne_of_gt hC,ne_of_gt hn] <;> ring
      _ ≤ ((allowed H F).card : ℝ)*(1/(C*Fintype.card X))*(1/Fintype.card X) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDensity (by positivity)) (by positivity)
      _ ≤ _ := hEach
  have hNorm := (ambient_seed_target_upper e R L hL hC hn hSeed).1
  apply Or.inr
  rw [padded_target_identity]
  calc
    _ = (α^3/(27*C)*Fintype.card X)/2 := by field_simp [ne_of_gt hC] <;> ring
    _ ≤ (∑ Q ∈ allowed H F, ψ Q*(1/Fintype.card X))/2 :=
      div_le_div_of_nonneg_right hBase (by norm_num)
    _ ≤ _ := by linarith only [hNorm]

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.childPaddedWeight_bounds
#print axioms TypedTriangle.Pasch.ambient_seed_target_upper
#print axioms TypedTriangle.Pasch.child_padded_target_upper
#print axioms TypedTriangle.Pasch.child_padded_target_lower_or_empty
