module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

def tripleSum (f : V → V → V → ℝ) : ℝ := ∑ b, ∑ c, ∑ a, f a b c
def firstCorrelation (f : V → V → V → ℝ) : ℝ := ∑ b, ∑ c, (∑ a, f a b c)^2
def secondCorrelation (f : V → V → V → ℝ) : ℝ :=
  ∑ a, ∑ a', ∑ c, (∑ b, f a b c*f a' b c)^2
def cubeCorrelation (f : V → V → V → ℝ) : ℝ :=
  ∑ a, ∑ a', ∑ b, ∑ b', ∑ c, (f a b c*f a' b c)*(f a b' c*f a' b' c)
def boxEight (f : V → V → V → ℝ) : ℝ :=
  ∑ a, ∑ a', ∑ b, ∑ b', (∑ c, (f a b c*f a' b c)*(f a b' c*f a' b' c))^2

private theorem sum_four_reorder (F : V → V → V → V → ℝ) :
    (∑ b, ∑ c, ∑ a, ∑ a', F a a' c b) = ∑ a, ∑ a', ∑ c, ∑ b, F a a' c b := by
  let e : (V × V × V × V) ≃ (V × V × V × V) :=
    ⟨fun p => (p.2.2.1,p.2.2.2,p.2.1,p.1),
     fun p => (p.2.2.2,p.2.2.1,p.1,p.2.1),
     by rintro ⟨b,c,a,a'⟩; rfl, by rintro ⟨a,a',c,b⟩; rfl⟩
  have he := Fintype.sum_equiv e
    (fun p => F p.2.2.1 p.2.2.2 p.2.1 p.1)
    (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2) (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using he

private theorem sum_three_reorder (F : V → V → V → ℝ) :
    (∑ c, ∑ b, ∑ b', F b b' c) = ∑ b, ∑ b', ∑ c, F b b' c := by
  let e : (V × V × V) ≃ (V × V × V) :=
    ⟨fun p => (p.2.1,p.2.2,p.1),fun p => (p.2.2,p.1,p.2.1),
     by rintro ⟨c,b,b'⟩; rfl, by rintro ⟨b,b',c⟩; rfl⟩
  have he := Fintype.sum_equiv e (fun p => F p.2.1 p.2.2 p.1)
    (fun p => F p.1 p.2.1 p.2.2) (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using he

theorem firstCorrelation_expand (f : V → V → V → ℝ) :
    firstCorrelation f = ∑ a, ∑ a', ∑ c, ∑ b, f a b c*f a' b c := by
  unfold firstCorrelation
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  exact sum_four_reorder _

theorem secondCorrelation_expand (f : V → V → V → ℝ) :
    secondCorrelation f = cubeCorrelation f := by
  unfold secondCorrelation cubeCorrelation
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro a' _
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  exact sum_three_reorder _

theorem boxEight_nonneg (f : V → V → V → ℝ) : 0 ≤ boxEight f := by
  apply sum_nonneg
  intro a _
  apply sum_nonneg
  intro a' _
  apply sum_nonneg
  intro b _
  apply sum_nonneg
  intro b' _
  exact sq_nonneg _

/-- Three applications of Cauchy--Schwarz give the unnormalized octahedral
box-count lower bound. No positivity or density premise is assumed on f. -/
theorem tripleSum_pow_eight_le_boxEight (f : V → V → V → ℝ) :
    (tripleSum f)^8 ≤ (Fintype.card V:ℝ)^18*boxEight f := by
  let n := (Fintype.card V:ℝ)
  have h1 : (tripleSum f)^2 ≤ (n*n)*firstCorrelation f := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s:=(univ:Finset (V × V))) (f:=fun p => ∑ a, f a p.1 p.2)
    simpa only [tripleSum,firstCorrelation,Fintype.sum_prod_type,card_univ,Fintype.card_prod,Nat.cast_mul] using hcs
  have h2 : (firstCorrelation f)^2 ≤ (n*(n*n))*secondCorrelation f := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s:=(univ:Finset (V × V × V)))
      (f:=fun p => ∑ b, f p.1 b p.2.2*f p.2.1 b p.2.2)
    rw [firstCorrelation_expand]
    simpa only [secondCorrelation,Fintype.sum_prod_type,card_univ,Fintype.card_prod,Nat.cast_mul] using hcs
  have h3 : (secondCorrelation f)^2 ≤ (n*(n*(n*n)))*boxEight f := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s:=(univ:Finset (V × V × V × V)))
      (f:=fun p => ∑ c, (f p.1 p.2.2.1 c*f p.2.1 p.2.2.1 c)*
        (f p.1 p.2.2.2 c*f p.2.1 p.2.2.2 c))
    rw [secondCorrelation_expand]
    simpa only [cubeCorrelation,boxEight,Fintype.sum_prod_type,card_univ,Fintype.card_prod,Nat.cast_mul] using hcs
  have hp1 := pow_le_pow_left₀ (sq_nonneg (tripleSum f)) h1 4
  have hp2 := pow_le_pow_left₀ (sq_nonneg (firstCorrelation f)) h2 2
  have h1' : (tripleSum f)^8 ≤ n^8*(firstCorrelation f)^4 := by
    convert hp1 using 1 <;> ring
  have h2' : (firstCorrelation f)^4 ≤ n^6*(secondCorrelation f)^2 := by
    convert hp2 using 1 <;> ring
  have h3' : (secondCorrelation f)^2 ≤ n^4*boxEight f := by
    convert h3 using 1 <;> ring
  calc (tripleSum f)^8 ≤ n^8*(firstCorrelation f)^4 := h1'
    _ ≤ n^8*(n^6*(secondCorrelation f)^2) := mul_le_mul_of_nonneg_left h2' (by positivity)
    _ = n^14*(secondCorrelation f)^2 := by ring
    _ ≤ n^14*(n^4*boxEight f) := mul_le_mul_of_nonneg_left h3' (by positivity)
    _ = n^18*boxEight f := by ring

#print axioms firstCorrelation_expand
#print axioms secondCorrelation_expand
#print axioms tripleSum_pow_eight_le_boxEight
end TypedTriangle.Pasch
