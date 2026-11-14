/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.FixedClassPatterns

/-! # Optimal leading entropy for a fixed balanced symbol-class pattern -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n k : ℕ}

theorem sum_csize (κ : Fin n → Fin k) : ∑ s, Hilton.csize κ s=n := by
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv κ)
  simpa only [Fintype.card_sigma,Fintype.card_fin,Hilton.csize] using hh

theorem fixed_class_pattern_entropy (κ : Fin n → Fin k) (cls : Fin n → Fin n → Fin k)
    (hreg : ∀ s, Regular (classGraph cls s) (Hilton.csize κ s))
    {δ : ℝ} (hδ : 0<δ) (hn : 0<n) (hsize : ∀ s, δ*n ≤ Hilton.csize κ s) :
    0<(classPatternTables κ cls).card ∧
      (n:ℝ)^2*(Real.log n+Real.log δ-2) ≤ Real.log (classPatternTables κ cls).card := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hspos : ∀ s, 0<Hilton.csize κ s := by
    intro s
    have hh : (0:ℝ)<Hilton.csize κ s := (mul_pos hδ hnR).trans_le (hsize s)
    exact_mod_cast hh
  let C : Fin k → ℕ := fun s => Fintype.card
    (PartialFactorization (classGraph cls s) (Hilton.csize κ s))
  have hC : ∀ s, 0<C s ∧
      (n:ℝ)*Hilton.csize κ s*(Real.log (Hilton.csize κ s)-2) ≤ Real.log (C s) :=
    fun s => factorization_log_lower (hreg s) hn (hspos s)
  have hprod : (0:ℝ)<((∏ s,C s:ℕ):ℝ) := by
    exact_mod_cast prod_pos (fun s _ => (hC s).1)
  have hcount := classPatternTables_count κ cls
  change (∏ s,C s) ≤ (classPatternTables κ cls).card at hcount
  have hpos : 0<(classPatternTables κ cls).card := by
    exact (prod_pos (fun s _ => (hC s).1)).trans_le hcount
  have hlog := Real.log_le_log hprod (show ((∏ s,C s:ℕ):ℝ)≤(classPatternTables κ cls).card by exact_mod_cast hcount)
  rw [Nat.cast_prod,Real.log_prod (fun s _ => (Nat.cast_pos.mpr (hC s).1).ne')] at hlog
  have hsum : ∑ s, (Hilton.csize κ s:ℝ)=(n:ℝ) := by exact_mod_cast sum_csize κ
  have hbase : ∀ s, Real.log n+Real.log δ ≤ Real.log (Hilton.csize κ s) := by
    intro s
    have hh := Real.log_le_log (mul_pos hδ hnR) (hsize s)
    rw [Real.log_mul hδ.ne' hnR.ne'] at hh
    linarith
  refine ⟨hpos,?_⟩
  calc
    _ = ∑ s, (n:ℝ)*Hilton.csize κ s*(Real.log n+Real.log δ-2) := by
      rw [← sum_mul,← mul_sum,hsum]
      ring
    _ ≤ ∑ s, (n:ℝ)*Hilton.csize κ s*(Real.log (Hilton.csize κ s)-2) := by
      apply sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (by linarith [hbase s]) (by positivity)
    _ ≤ ∑ s, Real.log (C s) := sum_le_sum (fun s _ => (hC s).2)
    _ ≤ _ := hlog

theorem card_filter_preimage {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] :
    #((univ:Finset A).filter (fun a => p (e a))) = #((univ:Finset B).filter p) := by
  apply card_bij (fun a _ => e a)
  · intro a ha
    simpa only [mem_filter,mem_univ,true_and] using ha
  · intro a _ b _ he
    exact e.injective he
  · intro b hb
    exact ⟨e.symm b,by simpa using hb,by simp⟩

theorem latin_class_graphs_regular (κ : Fin n → Fin k) (L : Fin n → Fin n → Fin n)
    (hL : _root_.STS.IsLatin L) :
    ∀ s, Regular (classGraph (fun r c => κ (L r c)) s) (Hilton.csize κ s) := by
  intro s
  constructor
  · intro r
    have hh := card_filter_preimage (Equiv.ofBijective (L r) (hL.1 r)) (fun z => κ z=s)
    simpa only [rowSet,classGraph,mem_filter,mem_univ,true_and,
      Equiv.ofBijective_apply,Fintype.card_subtype,Hilton.csize] using hh
  · intro c
    have hh := card_filter_preimage (Equiv.ofBijective (fun r => L r c) (hL.2 c)) (fun z => κ z=s)
    simpa only [colSet,classGraph,mem_filter,mem_univ,true_and,
      Equiv.ofBijective_apply,Fintype.card_subtype,Hilton.csize] using hh

end CDRBicolour.KBicolor.PrescribedCounting
