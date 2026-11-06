/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RawSeedDeletion
public import RequestProject.TypedTriangle.SampledRawWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! An approximate seed on a fixed sampled host survives the sparse holes
left by its paid child. This is a local transfer, not exact H1. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem approximate_seed_on_paid_child {V I : Type} [Fintype V]
    (J : Host V I) (F : Set (Multiset I)) (μ : Finset V → ℝ)
    (E : Finset (Sym2 V)) (d : ℕ) (C ξ : ℝ)
    (hC : 0 < C) (hn : 0 < (Fintype.card V : ℝ))
    (hE : E ⊆ edges J)
    (hμ : ∀ T, IsAllowed J F T →
      (1/(2*C))/Fintype.card V ≤ μ T ∧
        μ T ≤ (2*C)/Fintype.card V)
    (hload : ∀ e ∈ edges J, |bdry J F μ e-1| ≤ ξ)
    (hdeg : ∀ v, TypedTriangle.degIn (edges J \ E) v ≤ d) :
    let K := subHost J E
    ∃ μK : Finset V → ℝ,
      (∀ T, μK T ≠ 0 → IsAllowed K F T) ∧
      (∀ T, IsAllowed K F T →
        (1/(2*C))/Fintype.card V ≤ μK T ∧
          μK T ≤ (2*C)/Fintype.card V) ∧
      ∀ e ∈ edges K,
        |bdry K F μK e-1| ≤ ξ+2*(2*C)*d/Fintype.card V := by
  let B := edges J \ E
  let K := subHost J E
  let μK : Finset V → ℝ := fun T => if IsAllowed K F T then μ T else 0
  have hB : ∀ v, TypedTriangle.degIn B v ≤ d := hdeg
  have hnonneg : ∀ T, IsAllowed J F T →
      0 ≤ μ T ∧ μ T ≤ (2*C)/Fintype.card V := by
    intro T hT
    have h := hμ T hT
    constructor
    · exact (div_nonneg (by positivity) hn.le).trans h.1
    · exact h.2
  have hRaw := RawReference.load_after_deletion μ B d (2*C) ξ
    hn (by positivity) hnonneg hB hload
  have hRecover : edges J \ B = E := by
    dsimp [B]
    ext e
    simp only [mem_sdiff]
    have he : e ∈ E → e ∈ edges J := fun hp => hE hp
    tauto
  have hK : TypedTriangle.residual J B = K := by
    dsimp [TypedTriangle.residual, K]
    rw [hRecover]
  refine ⟨μK, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hNo
    have hZero : μK T = 0 := by exact if_neg hNo
    exact hT hZero
  · intro T hT
    have hJT : IsAllowed J F T :=
      isAllowed_mono (subHost_le J E) rfl hT
    have hValue : μK T = μ T := by exact if_pos hT
    rw [hValue]
    exact hμ T hJT
  · intro e he
    have hBoundary : bdry K F μK e = bdry K F μ e := by
      rw [bdry_eq_sum_triOn, bdry_eq_sum_triOn]
      apply sum_congr rfl
      intro T hT
      have hAllowed : IsAllowed K F T :=
        isAllowed_of_mem_allowed (mem_filter.mp hT).1
      simp only [μK, if_pos hAllowed]
    rw [hBoundary]
    exact hK ▸ hRaw e (hK ▸ he)

/-- The original diffuse seed supplies the raw profile on the *same* sample;
the sparse holes of the paid child are then charged to its local degree. -/
theorem sampled_paid_child_approx_seed {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (φ : Finset V → ℝ) (W : Finset V) (q C ξ : ℝ)
    (E : Finset (Sym2 {x // x ∈ W})) (d : ℕ)
    (hC : 0 < C) (hq : 0 < q)
    (hSeed : IsDiffuseSeed H F C φ)
    (hWlo : q*Fintype.card V/2 ≤ W.card)
    (hWhi : (W.card:ℝ) < 2*q*Fintype.card V)
    (hProfile : ∀ u v, H.G.Adj u v →
      |S07V48.sampW H.G H.lab F φ W u v/q-1| ≤ ξ)
    (hE : E ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
        Host {x // x ∈ W} I))
    (hdeg : ∀ v : {x // x ∈ W},
      TypedTriangle.degIn
        (edges (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
          Host {x // x ∈ W} I) \ E) v ≤ d) :
    let J : Host {x // x ∈ W} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let K := subHost J E
    ∃ μK : Finset {x // x ∈ W} → ℝ,
      (∀ T, μK T ≠ 0 → IsAllowed K F T) ∧
      (∀ T, IsAllowed K F T →
        (1/(2*C))/Fintype.card {x // x ∈ W} ≤ μK T ∧
          μK T ≤ (2*C)/Fintype.card {x // x ∈ W}) ∧
      ∀ e ∈ edges K,
        |bdry K F μK e-1| ≤ ξ+2*(2*C)*d/Fintype.card {x // x ∈ W} := by
  let J : Host {x // x ∈ W} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  letI : DecidableEq {x // x ∈ W} :=
    fun a b => Classical.propDecidable (a = b)
  have hProfileJ := RawReference.sampled_raw_profile hSeed hC hq
    W hWlo hWhi hProfile
  have hVpos : 0 < (Fintype.card V : ℝ) := by
    have hw : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    nlinarith [hWhi]
  have hWpos : 0 < (Fintype.card {x // x ∈ W} : ℝ) := by
    rw [Fintype.card_coe]
    nlinarith [hWlo, mul_pos hq hVpos]
  have hdegJ : ∀ v : {x // x ∈ W},
      TypedTriangle.degIn (edges J \ E) v ≤ d := by
    intro v
    convert hdeg v using 1
    unfold TypedTriangle.degIn
    congr 1
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    rfl
  exact approximate_seed_on_paid_child J F
    (RawReference.sampledWeights φ W q) E d C ξ hC hWpos hE
    hProfileJ.1 hProfileJ.2 hdegJ

#print axioms approximate_seed_on_paid_child
#print axioms sampled_paid_child_approx_seed

end TypedTriangle.CatalogNative
