/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalEnvelopeQuantitative
public import RequestProject.TypedTriangle.NativeDenseReference
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.RawReference

private theorem hasTri_of_approximate_load {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (ε : ℝ) (hε : ε < 1)
    (hLoad : ∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ε) :
    ∀ e ∈ edges H, HasTri H F e := by
  intro e he
  by_contra hNo
  have hZero : bdry H F μ e = 0 := by
    unfold bdry
    apply Finset.sum_eq_zero
    intro T hT
    have hAllowed : IsAllowed H F T := by simpa [allowed] using hT
    have hMissing : e ∉ triEdges T := fun heT => hNo ⟨T,hAllowed,heT⟩
    simp only [indR, if_neg hMissing, mul_zero]
  have hBound := hLoad e he
  rw [hZero] at hBound
  norm_num at hBound
  linarith

/-- A sparse future edge set can be retained literally inside a dense
basal reference. It need not itself be physical or decomposable. The
admissible degree of that set is fixed before the reference-hole precision. -/
theorem dense_reference_containing_sparse_edges {I : Type}
    (F : Set (Multiset I)) (a b α : ℝ) (h : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ η : ℝ, 0 < η →
      ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ n₀ : ℕ,
        ∀ {V : Type} [Fintype V] (H : Host V I) (μ : Finset V → ℝ)
          (E B : Finset (Sym2 V)) (dE dB : ℕ),
          n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
          (∀ T, IsAllowed H F T →
            a / Fintype.card V ≤ μ T ∧ μ T ≤ b / Fintype.card V) →
          (∀ e ∈ edges H, |bdry H F μ e - 1| ≤ ε) →
          E ⊆ edges H → Disjoint E B →
          (∀ v, degIn E v ≤ dE) → (dE : ℝ) ≤ ρ * Fintype.card V →
          (∀ v, degIn B v ≤ dB) → (dB : ℝ) ≤ γ * Fintype.card V →
          ∃ (E₀ : Finset (Sym2 V)) (D₀ : Finset (Finset V)),
            E ⊆ E₀ ∧ E₀ ⊆ edges H ∧ IsDecomposition H F E₀ D₀ ∧
            Disjoint E₀ B ∧
            ∀ v, (degIn (edges H \ E₀) v : ℝ) ≤ η * Fintype.card V := by
  obtain ⟨c,hc,δ,hδ,nEnv,hEnv⟩ := Envelope.uniform_envelope_of_H3 α hα
  obtain ⟨θ,hθ,hRef⟩ := dense_reference_containing_stock F a b α h ha hab hα
  let ρ := min δ (θ / (2 * ((c : ℝ) + 1)))
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  refine ⟨ρ,hρ,?_⟩
  intro η hη
  obtain ⟨εRef,γRef,hεRef,hγRef,nRef,hMake⟩ := hRef η hη
  let ε := min εRef (1/2)
  let γ := min γRef δ
  let n₀ := max nEnv (max nRef ⌈2 * (c : ℝ) / θ⌉₊)
  refine ⟨ε,γ,lt_min hεRef (by norm_num),lt_min hγRef hδ,n₀,?_⟩
  intro V _ H μ E B dE dB hn h3 h4 hWeights hLoad hE hEB hEdeg hEcap hBdeg hBcap
  have hnEnv : nEnv ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnRef : nRef ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRound : ⌈2 * (c : ℝ) / θ⌉₊ ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hTri := hasTri_of_approximate_load H F μ ε
    ((min_le_right _ _).trans_lt (by norm_num)) hLoad
  obtain ⟨W,hW,hBasal,hWdeg⟩ := hEnv H F hnEnv h3 E B ∅ dE dB
    (by intro v; simpa only [SelSimul.edeg,degIn] using hEdeg v)
    (by intro v; simpa only [SelSimul.edeg,degIn] using hBdeg v)
    (hEcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
    (hBcap.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)))
    (by simp; positivity) (fun e he => hTri e (hE he))
  obtain ⟨DS,hDS⟩ := hBasal
  let S := E ∪ W
  let dS := dE + c * (dE + 1)
  have hS : S ⊆ edges H := by
    intro e he
    obtain ⟨T,hT,heT⟩ := hDS.exists_mem he
    exact triEdges_subset_edges (hDS.1 T hT) heT
  have hSB : Disjoint S B :=
    disjoint_union_left.mpr ⟨hEB,hW.mono_right subset_union_right⟩
  have hSdeg : ∀ v, degIn S v ≤ dS := by
    intro v
    have hUnion := SelSimul.edeg_union_le E W v
    have hWing := hWdeg v
    simpa only [S,dS,SelSimul.edeg,degIn] using
      hUnion.trans (Nat.add_le_add (hEdeg v) hWing)
  have hRound : (c : ℝ) ≤ θ / 2 * Fintype.card V := by
    have hnReal : (⌈2 * (c : ℝ) / θ⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hnRound
    have hCeil := (Nat.le_ceil (2 * (c : ℝ) / θ)).trans hnReal
    have hMul := (div_le_iff₀ hθ).mp hCeil
    nlinarith
  have hCoef : ((c : ℝ) + 1) * ρ ≤ θ / 2 := by
    have hUpper : ρ ≤ θ / (2 * ((c : ℝ) + 1)) := min_le_right _ _
    have hMul := (le_div_iff₀ (by positivity : 0 < 2 * ((c : ℝ) + 1))).mp hUpper
    nlinarith
  have hScap : (dS : ℝ) ≤ θ * Fintype.card V := by
    have hScale := mul_le_mul_of_nonneg_right hCoef
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    have hDE := mul_le_mul_of_nonneg_left hEcap
      (show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity)
    dsimp only [dS]
    push_cast
    nlinarith
  obtain ⟨E₀,D₀,hSE,hE₀,hDec,_,hAvoid,hHole⟩ :=
    hMake H μ S B DS dS dB hnRef h4 hWeights
      (fun e he => (hLoad e he).trans (min_le_left _ _)) hS hDS hSB hSdeg hScap hBdeg
      (hBcap.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)))
  exact ⟨E₀,D₀,subset_union_left.trans hSE,hE₀,hDec,hAvoid,hHole⟩

#print axioms dense_reference_containing_sparse_edges
end TypedTriangle.RawReference
