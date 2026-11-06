module
public import RequestProject.TypedTriangle.PaschHingeAssignmentFamilies
public import RequestProject.TypedTriangle.PaschSupportCoverage
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def supportIncrementCost (R : Finset (Finset V)) (U W : Finset V) : ℕ :=
  ∑ Q ∈ ((U ∪ W).powersetCard 3).filter (fun Q => ¬ Q ⊆ U), rootedCount (insert Q R) Q

/-- Uniform in the host, the forbidden resources, and the hinge order chosen by H4. -/
def hingePotentialCost (α : ℝ) (h Ub L : ℕ) : ℝ :=
  (Nat.choose (Ub+h) 3:ℝ)*(2*(2:ℝ)^Nat.choose h 2)*(L:ℝ)^3/α

/-- The actual robust H4 family supplies a low-potential hinge. R is the
fixed previous mode universe; all triples newly added to the old support are paid together. -/
theorem exists_low_cost_robust_hinge {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH4 : HingeCond H F α h)
    {u v a b : V} (hab : a ≠ b)
    (hTa : IsAllowed H F {u,v,a}) (hTb : IsAllowed H F {u,v,b})
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (U : Finset V) (Ub : ℕ) (hU : U.card ≤ Ub) (hRoots : ({u,v,a,b}:Finset V) ⊆ U)
    (Z : Finset V) (B : Finset (Sym2 V)) (d : ℕ) (hdeg : ∀ x, degIn B x ≤ d)
    (hB : s(a,b) ∉ B) (hWin : ((Z.card:ℝ)+5*d)*2^Nat.choose h 2 ≤ α/2*Fintype.card V) :
    ∃ i : ℕ, 6 ≤ i ∧ i ≤ h ∧ ∃ J ∈ hinges H F u v a b i,
      (∀ z ∈ Z, z ∈ support J → z ∈ ({u,v,a,b}:Finset V)) ∧ Disjoint J B ∧
      (supportIncrementCost R U (support J):ℝ) ≤ hingePotentialCost α h Ub L := by
  obtain ⟨i,hi6,hih,P,hMass,hWitness⟩ := exists_robust_hinge_assignment_family
    hα hH4 hab hTa hTb Z B d hdeg hB hWin
  let A := {v // v ∈ U}
  let base : A → V := Subtype.val
  have hBase : univ.image base = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,_,rfl⟩ := mem_image.mp hx
      exact y.property
    · intro hx
      exact mem_image.mpr ⟨⟨x,hx⟩,mem_univ _,rfl⟩
  let κ : ℝ := α/(2*(2:ℝ)^Nat.choose i 2)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hnNat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast hnNat
  have hN : (0:ℝ) < Fintype.card (Fin (i-4) → V) := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using pow_pos hn (i-4)
  have hPool : κ*(Fintype.card (Fin (i-4) → V):ℝ) ≤ P.card := by
    simpa only [κ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using hMass
  obtain ⟨f,hf,hCost⟩ := exists_low_support_increment R L hL base P κ hκ hN hPool
  obtain ⟨_,_,J,hJ,hFresh,hJB,hFull⟩ := hWitness f hf
  have hUnion : U ∪ support J = U ∪ univ.image f := by
    rw [hFull,←union_assoc,union_eq_left.mpr hRoots]
  have hNew : ((U ∪ support J).powersetCard 3).filter (fun Q => ¬ Q ⊆ U) =
      newSupportTriples base f := by
    unfold newSupportTriples
    rw [hBase,hUnion]
  have hActual : (supportIncrementCost R U (support J):ℝ) =
      ∑ Q ∈ newSupportTriples base f, (rootedCount (insert Q R) Q:ℝ) := by
    unfold supportIncrementCost
    rw [hNew,Nat.cast_sum]
  have hCost' : (∑ Q ∈ newSupportTriples base f, (rootedCount (insert Q R) Q:ℝ)) ≤
      ((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ := by
    simpa only [A,Fintype.card_coe,Fintype.card_fin] using hCost
  have hChooseNat : Nat.choose (U.card+(i-4)) 3 ≤ Nat.choose (Ub+h) 3 :=
    Nat.choose_le_choose 3 (Nat.add_le_add hU ((Nat.sub_le i 4).trans hih))
  have hChoose : (Nat.choose (U.card+(i-4)) 3:ℝ) ≤ (Nat.choose (Ub+h) 3:ℝ) := by
    exact_mod_cast hChooseNat
  have hPow : (2:ℝ)^Nat.choose i 2 ≤ (2:ℝ)^Nat.choose h 2 :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hih)
  have hNumer : (Nat.choose (U.card+(i-4)) 3:ℝ)*(2*(2:ℝ)^Nat.choose i 2)*(L:ℝ)^3 ≤
      (Nat.choose (Ub+h) 3:ℝ)*(2*(2:ℝ)^Nat.choose h 2)*(L:ℝ)^3 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hChoose (mul_le_mul_of_nonneg_left hPow (by norm_num))
      (by positivity) (by positivity)
  have hUniform : ((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ ≤ hingePotentialCost α h Ub L := by
    calc ((Nat.choose (U.card+(i-4)) 3:ℝ)*(L:ℝ)^3)/κ
        = ((Nat.choose (U.card+(i-4)) 3:ℝ)*(2*(2:ℝ)^Nat.choose i 2)*(L:ℝ)^3)/α := by
          dsimp only [κ]
          field_simp [ne_of_gt hα,ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) (Nat.choose i 2))] <;> ring
      _ ≤ hingePotentialCost α h Ub L := div_le_div_of_nonneg_right hNumer hα.le
  exact ⟨i,hi6,hih,J,hJ,hFresh,hJB,hActual.trans_le (hCost'.trans hUniform)⟩

#print axioms exists_low_cost_robust_hinge
end TypedTriangle.Pasch
