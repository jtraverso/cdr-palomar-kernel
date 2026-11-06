module
public import RequestProject.S07V37.FinitePresentation
public import RequestProject.TypedTriangle.ExplicitKernelLinearBound
public import RequestProject.TypedTriangle.QuotientBoxExplicitBound
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Submodule Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace S07V37.Explicit
open TypedTriangle.GroupingExplicit TypedTriangle.QuotientBox

def presLBound (d E : ℕ) : ℕ := kernelBound d E
def presKBound (m d E : ℕ) : ℕ := (2 * presLBound d E + 1) ^ m

private abbrev SignedIndex (ι : Type) {d : ℕ} (S : Finset (Fin d → ℤ)) :=
  (ι ⊕ ι) ⊕ (S ⊕ S)

private def signedColumns {ι : Type} {d : ℕ} (c : ι → Fin d → ℤ)
    (S : Finset (Fin d → ℤ)) : SignedIndex ι S → Fin d → ℤ :=
  Sum.elim (Sum.elim c (fun i => -c i)) (Sum.elim (fun s => -s.val) Subtype.val)

private def projection {ι : Type} {d : ℕ} {S : Finset (Fin d → ℤ)}
    (u : SignedIndex ι S → ℕ) : ι → ℤ :=
  fun i => (u (.inl (.inl i)) : ℤ) - (u (.inl (.inr i)) : ℤ)

private theorem signed_parts {κ : Type} [Fintype κ] {d : ℕ}
    (f : κ → ℤ) (A : κ → Fin d → ℤ) :
    (∑ i, ((f i).toNat : ℤ) • A i) - (∑ i, ((-f i).toNat : ℤ) • A i) =
      ∑ i, f i • A i := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sub_smul]
  congr 1
  omega

private theorem projection_mem {ι : Type} [Fintype ι] {d : ℕ}
    (c : ι → Fin d → ℤ) (S : Finset (Fin d → ℤ)) (u : SignedIndex ι S → ℕ)
    (hz : (∑ k, (u k : ℤ) • signedColumns c S k) = 0) :
    projection u ∈ presMod c (S : Set (Fin d → ℤ)) := by
  have heq : (∑ i, projection u i • c i) =
      (∑ s : S, (u (.inr (.inl s)) : ℤ) • s.val) -
        (∑ s : S, (u (.inr (.inr s)) : ℤ) • s.val) := by
    simp only [Fintype.sum_sum_type, signedColumns, Sum.elim_inl, Sum.elim_inr,
      smul_neg, sum_neg_distrib] at hz
    simp only [projection, sub_smul, sum_sub_distrib]
    linear_combination hz
  apply mem_presMod.mpr
  rw [heq]
  apply Submodule.sub_mem
  · exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (subset_span s.property))
  · exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (subset_span s.property))

private theorem projection_l1 {ι : Type} [Fintype ι] {d : ℕ}
    {S : Finset (Fin d → ℤ)} (u : SignedIndex ι S → ℕ) :
    l1c (projection u) ≤ (∑ k, u k : ℕ) := by
  have hpart : (∑ i : ι, (u (.inl (.inl i)) + u (.inl (.inr i)))) ≤ ∑ k, u k := by
    simp only [Fintype.sum_sum_type, sum_add_distrib]
    omega
  calc
    l1c (projection u) ≤ ∑ i : ι,
        ((u (.inl (.inl i)) : ℤ) + (u (.inl (.inr i)) : ℤ)) := by
      apply sum_le_sum
      intro i _
      change |(u (.inl (.inl i)) : ℤ) - (u (.inl (.inr i)) : ℤ)| ≤ _
      simpa using (abs_sub (u (.inl (.inl i)) : ℤ) (u (.inl (.inr i)) : ℤ))
    _ = ((∑ i : ι, (u (.inl (.inl i)) + u (.inl (.inr i))) : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ (∑ k, u k : ℕ) := by exact_mod_cast hpart

/-- Actual generators of the exact integer preimage module, with an
    elementary norm bound, independent of a Noetherian generating-set choice. -/
theorem presentation_uniform_explicit {ι : Type} [Fintype ι] {d : ℕ}
    (E : ℕ) (c : ι → Fin d → ℤ) (hc : ∀ i k, |c i k| ≤ (E : ℤ))
    (S : Finset (Fin d → ℤ)) (hS : ∀ s ∈ S, ∀ k, |s k| ≤ (E : ℤ)) :
    ∃ Z : Finset (ι → ℤ), Z.card ≤ presKBound (Fintype.card ι) d E ∧
      (∀ z ∈ Z, l1c z ≤ (presLBound d E : ℤ)) ∧
      span ℤ (Z : Set (ι → ℤ)) = presMod c (S : Set (Fin d → ℤ)) := by
  let G := presLBound d E
  let e := Fintype.equivFin ι
  let B : Finset (ι → ℤ) := (box (Fintype.card ι) G).image (fun v i => v (e i))
  let Z := B.filter (fun z => z ∈ presMod c (S : Set (Fin d → ℤ)) ∧ l1c z ≤ (G : ℤ))
  have hSmall (z : ι → ℤ) (hz : z ∈ presMod c (S : Set (Fin d → ℤ)))
      (hl : l1c z ≤ (G : ℤ)) : z ∈ Z := by
    apply mem_filter.mpr
    refine ⟨?_, hz, hl⟩
    apply mem_image.mpr
    refine ⟨fun j => z (e.symm j), mem_box.mpr ?_, ?_⟩
    · intro j
      exact (single_le_sum (fun i _ => abs_nonneg (z i)) (mem_univ (e.symm j))).trans hl
    · funext i
      simp
  have hA : ∀ i k, |signedColumns c S i k| ≤ (E : ℤ) := by
    intro i k
    rcases i with (i | i) | (s | s)
    · exact hc i k
    · simpa only [signedColumns, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, abs_neg] using hc i k
    · simpa only [signedColumns, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, abs_neg] using hS s.val s.property k
    · exact hS s.val s.property k
  have hKernel : ∀ u : SignedIndex ι S → ℕ,
      (∑ k, (u k : ℤ) • signedColumns c S k) = 0 →
      projection u ∈ span ℤ (Z : Set (ι → ℤ)) := by
    suffices H : ∀ n : ℕ, ∀ u : SignedIndex ι S → ℕ, (∑ k, u k) = n →
        (∑ k, (u k : ℤ) • signedColumns c S k) = 0 →
        projection u ∈ span ℤ (Z : Set (ι → ℤ)) by
      intro u hu
      exact H _ u rfl hu
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hnorm hz
      by_cases hu : u = 0
      · have hp : projection u = (0 : ι → ℤ) := by
          subst u
          funext i
          simp [projection]
        rw [hp]
        exact Submodule.zero_mem _
      obtain ⟨v, hvu, hv, hvzero, hvsize⟩ := kernel_small_subvector d E (signedColumns c S) u hA hu hz
      let w : SignedIndex ι S → ℕ := fun i => u i - v i
      have hsplit : ∀ i, w i + v i = u i := fun i => Nat.sub_add_cancel (hvu i)
      have hmass : (∑ i, w i) + (∑ i, v i) = ∑ i, u i := by
        rw [← sum_add_distrib]
        exact sum_congr rfl (fun i _ => hsplit i)
      have hvpos : 0 < ∑ i, v i := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        have hi' : 0 < v i := Nat.pos_of_ne_zero (by simpa only [Pi.zero_apply] using hi)
        exact hi'.trans_le (single_le_sum (fun j _ => Nat.zero_le (v j)) (mem_univ i))
      have hwzero : (∑ i, (w i : ℤ) • signedColumns c S i) = 0 := by
        have hh : (∑ i, (w i : ℤ) • signedColumns c S i) +
            (∑ i, (v i : ℤ) • signedColumns c S i) = ∑ i, (u i : ℤ) • signedColumns c S i := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro i _
          rw [← add_smul, ← Nat.cast_add, hsplit i]
        simpa only [hvzero, hz, add_zero] using hh
      have hw := ih _ (by omega : (∑ i, w i) < n) w rfl hwzero
      have hvnorm : l1c (projection v) ≤ (G : ℤ) :=
        (projection_l1 v).trans (by exact_mod_cast hvsize)
      have hvmem : projection v ∈ span ℤ (Z : Set (ι → ℤ)) :=
        subset_span (hSmall _ (projection_mem c S v hvzero) hvnorm)
      have hp : projection u = projection w + projection v := by
        funext i
        dsimp only [projection, w, Pi.add_apply]
        rw [Nat.cast_sub (hvu (.inl (.inl i))), Nat.cast_sub (hvu (.inl (.inr i)))]
        ring
      rw [hp]
      exact Submodule.add_mem _ hw hvmem
  refine ⟨Z, ?_, (fun z hz => (mem_filter.mp hz).2.2), le_antisymm ?_ ?_⟩
  · exact (card_filter_le _ _).trans (card_image_le.trans (by
      rw [card_box]
      exact le_rfl))
  · apply span_le.mpr
    intro z hz
    exact (mem_filter.mp hz).2.1
  · intro t ht
    obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp (mem_presMod.mp ht)
    let u : SignedIndex ι S → ℕ :=
      Sum.elim (Sum.elim (fun i => (t i).toNat) (fun i => (-t i).toNat))
        (Sum.elim (fun s => (a s).toNat) (fun s => (-a s).toNat))
    have hp : projection u = t := by
      funext i
      dsimp [projection, u]
      omega
    have hz : (∑ k, (u k : ℤ) • signedColumns c S k) = 0 := by
      simp only [Fintype.sum_sum_type, signedColumns, u, Sum.elim_inl, Sum.elim_inr,
        smul_neg, sum_neg_distrib]
      have hleft := signed_parts t c
      have hright := signed_parts a (Subtype.val : S → Fin d → ℤ)
      linear_combination hleft - hright - ha
    rw [← hp]
    exact hKernel u hz

#print axioms presentation_uniform_explicit
end S07V37.Explicit
