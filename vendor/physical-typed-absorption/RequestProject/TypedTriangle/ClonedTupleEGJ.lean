module
public import RequestProject.TypedTriangle.ClonedTupleDegrees
public import RequestProject.PaschEGJ13.Theorem13
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone

variable {E ι : Type*} [Fintype E] [Fintype ι]

/-- The actual tuple mass of the integer clone hypergraph, expressed on bases. -/
def tupleMass (P : ι → Finset E) (m : ι → ℕ) (w : Finset ι → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ S ∈ (univ.powersetCard ℓ).filter (BaseMatching P), w S * ∏ i ∈ S, (m i : ℝ)

/-- Fixed indices have no multiplicity factor in a tuple extension. -/
def tupleExtensionMass (P : ι → Finset E) (m : ι → ℕ) (w : Finset ι → ℝ)
    (ℓ : ℕ) (R : Finset ι) : ℝ :=
  ∑ S ∈ (univ.powersetCard ℓ).filter (fun S => R ⊆ S ∧ BaseMatching P S),
    w S * ∏ i ∈ S \ R, (m i : ℝ)

theorem tupleMass_nonneg (P : ι → Finset E) (m : ι → ℕ) (w : Finset ι → ℝ)
    (hw : ∀ S, 0 ≤ w S) (ℓ : ℕ) : 0 ≤ tupleMass P m w ℓ := by
  exact sum_nonneg (fun S _ => mul_nonneg (hw S) (prod_nonneg (fun _ _ => Nat.cast_nonneg _)))

/-- EGJ 1.3 constructs one matching controlling all eligible tuple weights.
The hypotheses are integer degree bounds and explicit base tuple sums; no
matching or regularization provider is assumed. -/
theorem tuple_matching_from_integer_multiplicities
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (r : ℕ) (hr : 1 ≤ r)
    (L : ℕ) (hL : 1 ≤ L) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → 1 ≤ D →
    ∀ (E ι : Type) [Fintype E] [Fintype ι] (P : ι → Finset E) (m : ι → ℕ),
      (∀ i, (P i).card = r) →
      (∀ e, ((∑ i, if e ∈ P i then m i else 0 : ℕ) : ℝ) ≤ D) →
      (∀ e f, e ≠ f →
        ((∑ i, if e ∈ P i ∧ f ∈ P i then m i else 0 : ℕ) : ℝ) ≤ D ^ (1 - δ)) →
      ((∑ i, m i : ℕ) : ℝ) ≤ Real.exp (D ^ ((δ / (50 * L ^ 2 * (r + 1) ^ 2)) ^ 2)) →
      ∀ (κ : ℕ → Type) [∀ ℓ, Fintype (κ ℓ)] (W : (ℓ : ℕ) → κ ℓ → Finset ι → ℝ),
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k S, 0 ≤ W ℓ k S) →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → (Fintype.card (κ ℓ) : ℝ) ≤
        Real.exp (D ^ ((δ / (50 * L ^ 2 * (r + 1) ^ 2)) ^ 2))) →
      ∃ C : Finset (Copy m),
        (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) ∧
        ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k : κ ℓ,
          (∀ j, 1 ≤ j → j ≤ ℓ → ∀ R : Finset ι, R.card = j →
            tupleExtensionMass P m (W ℓ k) ℓ R * D ^ ((j : ℝ) + δ) ≤
              tupleMass P m (W ℓ k) ℓ) →
          |PatternStatistics.statistic (W ℓ k) ℓ (copyProjection m C) -
              tupleMass P m (W ℓ k) ℓ / D ^ ℓ| ≤
            D ^ (-(δ / (50 * L ^ 2 * (r + 1) ^ 2))) *
              (tupleMass P m (W ℓ k) ℓ / D ^ ℓ) := by
  obtain ⟨D₀, hEGJ⟩ := Pseudorandom.theorem_1_3 δ hδ hδ1 (r + 1) (by omega) L hL
  refine ⟨D₀, ?_⟩
  intro D hD₀ hD E ι _ _ P m hcard hdeg hcode hsize κ _ W hW hκ
  have hP : ∀ i, (P i).Nonempty := fun i => card_pos.mp (by rw [hcard]; omega)
  have hpow : 1 ≤ D ^ (1 - δ) := Real.one_le_rpow hD (by linarith)
  have hdegree : ∀ v : E ⊕ Copy m,
      (Pseudorandom.degree (hypergraph P m) v : ℝ) ≤ D := by
    intro v
    cases v with
    | inl e => simpa only [degree_left] using hdeg e
    | inr c => simpa only [degree_right, Nat.cast_one] using hD
  have hcodegree : ∀ u v : E ⊕ Copy m, u ≠ v →
      (Pseudorandom.codegree (hypergraph P m) u v : ℝ) ≤ D ^ (1 - δ) := by
    intro u v huv
    cases u with
    | inl e =>
      cases v with
      | inl f => simpa only [codegree_left] using hcode e f (by simpa using huv)
      | inr c => exact (show (Pseudorandom.codegree (hypergraph P m)
          (Sum.inl e) (Sum.inr c) : ℝ) ≤ 1 by
            exact_mod_cast codegree_mixed_le P m e c).trans hpow
    | inr c =>
      cases v with
      | inl e =>
        have heq : Pseudorandom.codegree (hypergraph P m) (Sum.inr c) (Sum.inl e) =
            Pseudorandom.codegree (hypergraph P m) (Sum.inl e) (Sum.inr c) := by
          simp only [Pseudorandom.codegree, and_comm]
        rw [heq]
        exact (show (Pseudorandom.codegree (hypergraph P m)
          (Sum.inl e) (Sum.inr c) : ℝ) ≤ 1 by
            exact_mod_cast codegree_mixed_le P m e c).trans hpow
      | inr d =>
        rw [codegree_right_eq_zero P m (by simpa using huv), Nat.cast_zero]
        exact le_trans zero_le_one hpow
  obtain ⟨M, hMH, hM, hweights⟩ := hEGJ D hD₀ (E ⊕ Copy m) (hypergraph P m)
    (hypergraph_uniform P m hcard) hdegree hcodegree
    (by simpa only [hypergraph_card, Nat.cast_add, Nat.cast_one] using hsize)
    κ (fun ℓ k => tupleLiftedWeight P m (W ℓ k))
    (by simpa only [Nat.cast_add, Nat.cast_one] using hκ)
    (by intro ℓ hℓ hℓL k S _; exact tupleLiftedWeight_nonneg P m _ (hW ℓ hℓ hℓL k) S)
    (by
      intro ℓ _ _ k S _ hne
      by_contra hn
      exact hne (tupleLiftedWeight_clean P m _ S hn))
  obtain ⟨C, hMC, hDis, _⟩ := extract_matching P m hMH hM
  refine ⟨C, hDis, ?_⟩
  intro ℓ hℓ hℓL k heligible
  have hb := hweights ℓ hℓ hℓL k (by
    intro j hj hjℓ T hT
    obtain ⟨hTH, hTcard⟩ := mem_powersetCard.mp hT
    by_cases hTM : Pseudorandom.IsMatching T
    · rw [tdeg_lift_hypergraph P m hP _ _ hTH hTM, tweight_lift_hypergraph]
      exact heligible j hj hjℓ (tupleProjection P m T)
        ((tupleProjection_card_of_matching P m hP hTH hTM).trans hTcard)
    · rw [tdeg_lift_of_not_matching P m _ _ T hTM, zero_mul, tweight_lift_hypergraph]
      exact tupleMass_nonneg P m _ (hW ℓ hℓ hℓL k) ℓ)
  rw [tweight_lift_matching P m hP _ _ hMH hM, tweight_lift_hypergraph] at hb
  have hproj : tupleProjection P m M = copyProjection m C := by
    rw [hMC]
    exact recoverPackets_image P m C |> congrArg (copyProjection m)
  rw [hproj] at hb
  simpa only [Nat.cast_add, Nat.cast_one, tupleMass] using hb

#print axioms tupleMass_nonneg
#print axioms tuple_matching_from_integer_multiplicities
end TypedTriangle.WeightedClone
