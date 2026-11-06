module
public import RequestProject.TypedTriangle.PaschBoxCount
public import RequestProject.TypedTriangle.PaschHostDensity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def boxIndicator (H : Host V I) (F : Set (Multiset I)) (a b c : V) : ℝ :=
  if IsAllowed H F {a,b,c} then 1 else 0

/-- Three pairs occupy consecutive positions in the labelled six-tuple. -/
def boxAllowed (H : Host V I) (F : Set (Multiset I)) (f : Fin 6 → V) : Prop :=
  ∀ i j k : Fin 2, IsAllowed H F
    {f ⟨i.val,by omega⟩,f ⟨2+j.val,by omega⟩,f ⟨4+k.val,by omega⟩}

private def boxTerm (H : Host V I) (F : Set (Multiset I)) (q : Fin 6 → V) : ℝ :=
  ((boxIndicator H F (q 0) (q 2) (q 4)*boxIndicator H F (q 1) (q 2) (q 4))*
   (boxIndicator H F (q 0) (q 3) (q 4)*boxIndicator H F (q 1) (q 3) (q 4)))*
  ((boxIndicator H F (q 0) (q 2) (q 5)*boxIndicator H F (q 1) (q 2) (q 5))*
   (boxIndicator H F (q 0) (q 3) (q 5)*boxIndicator H F (q 1) (q 3) (q 5)))

private theorem boxTerm_eq (H : Host V I) (F : Set (Multiset I)) (q : Fin 6 → V) :
    boxTerm H F q = if boxAllowed H F q then 1 else 0 := by
  by_cases h : boxAllowed H F q
  · have hAll := h
    simp only [boxAllowed,Fin.forall_fin_two] at hAll
    rcases hAll with ⟨⟨⟨h000,h001⟩,h010,h011⟩,⟨h100,h101⟩,h110,h111⟩
    simp_all [boxTerm,boxIndicator]
  · rw [if_neg h]
    have hNot : ∃ i j k : Fin 2, ¬ IsAllowed H F
        {q ⟨i.val,by omega⟩,q ⟨2+j.val,by omega⟩,q ⟨4+k.val,by omega⟩} := by
      simpa only [boxAllowed,not_forall] using h
    obtain ⟨i,j,k,hBad⟩ := hNot
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [boxTerm,boxIndicator] at hBad ⊢ <;> simp_all

private def sixTupleEquiv : (Fin 6 → V) ≃ V × V × V × V × V × V :=
  ⟨fun q => (q 0,q 1,q 2,q 3,q 4,q 5),
   fun p => ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2],
   by intro q; funext i; fin_cases i <;> rfl,
   by rintro ⟨a,a',b,b',c,c'⟩; rfl⟩

/-- The analytic octahedral box moment is exactly the number of labelled
six-tuples whose eight cross-triples are allowed. Repeated vertices are included. -/
theorem boxIndicator_count (H : Host V I) (F : Set (Multiset I)) :
    boxEight (boxIndicator H F) =
      ((univ.filter (boxAllowed H F)).card : ℝ) := by
  have hSum := Fintype.sum_equiv (sixTupleEquiv (V := V))
    (fun q => boxTerm H F q)
    (fun p => boxTerm H F ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2])
    (fun q => (congrArg (boxTerm H F) ((sixTupleEquiv (V := V)).left_inv q)).symm)
  have hCount : (∑ q : Fin 6 → V, boxTerm H F q) =
      ((univ.filter (boxAllowed H F)).card : ℝ) := by
    simp_rw [boxTerm_eq]
    simp
  rw [← hCount,hSum]
  simp only [Fintype.sum_prod_type]
  unfold boxEight
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  rfl

/-- The ordered triangle indicator already has density at least alpha cubed:
the growth triples are ordered, so there is no factor of 27 at this step. -/
theorem tripleSum_boxIndicator_lower {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 ≤ α) {a b c : V}
    (hT : IsAllowed H F {a,b,c}) :
    (α*(Fintype.card V : ℝ))^3 ≤ tripleSum (boxIndicator H F) := by
  let A := growthTriples H a b c
  have hMass := growthTriples_card_lower hH3 hα hT
  have hSum : (A.card : ℝ) = ∑ z ∈ A, boxIndicator H F z.1 z.2.1 z.2.2 := by
    have hOne : ∀ z ∈ A, boxIndicator H F z.1 z.2.1 z.2.2 = 1 := by
      intro z hz
      exact if_pos (growthTriple_allowed hT hz)
    rw [sum_congr rfl hOne]
    simp
  have hUpper : (∑ z ∈ A, boxIndicator H F z.1 z.2.1 z.2.2) ≤
      ∑ z : Σ _ : V, Σ _ : V, V, boxIndicator H F z.1 z.2.1 z.2.2 := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro z _ _
    unfold boxIndicator
    split_ifs <;> norm_num
  have hOrdered : (∑ z : Σ _ : V, Σ _ : V, V, boxIndicator H F z.1 z.2.1 z.2.2) =
      tripleSum (boxIndicator H F) := by
    simp only [Fintype.sum_sigma,tripleSum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  exact hMass.trans (hSum.trans_le (hUpper.trans_eq hOrdered))

/-- Positive ordered triangle density yields a labelled octahedral count
directly from H3, with no additional density assumption. -/
theorem boxAllowed_card_lower {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (hH3 : CommonNbrCond H F α) (hα : 0 ≤ α) (hn : 0 < Fintype.card V)
    {a b c : V} (hT : IsAllowed H F {a,b,c}) :
    α^24*(Fintype.card V : ℝ)^6 ≤ ((univ.filter (boxAllowed H F)).card : ℝ) := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hLower := tripleSum_boxIndicator_lower hH3 hα hT
  have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ (α*(Fintype.card V : ℝ))^3) hLower 8
  apply (mul_le_mul_iff_right₀ (pow_pos hnR 18)).mp
  calc
    (Fintype.card V : ℝ)^18*(α^24*(Fintype.card V : ℝ)^6) =
        ((α*(Fintype.card V : ℝ))^3)^8 := by ring
    _ ≤ (tripleSum (boxIndicator H F))^8 := hPow
    _ ≤ (Fintype.card V : ℝ)^18*boxEight (boxIndicator H F) :=
      tripleSum_pow_eight_le_boxEight _
    _ = _ := by rw [boxIndicator_count]

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.boxIndicator_count
#print axioms TypedTriangle.Pasch.tripleSum_boxIndicator_lower
#print axioms TypedTriangle.Pasch.boxAllowed_card_lower
