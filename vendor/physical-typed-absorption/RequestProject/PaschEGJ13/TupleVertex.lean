/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.LocalSum
public import RequestProject.Pseudorandom.VertexPartition
public import RequestProject.PaschEGJ13.TupleMatching
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Step 1 of Theorem 1.3: tuple weights under a random vertex partition

For a random vertex colouring `τ : V → [p]` and a set `S` of `ℓ` pairwise disjoint edges, the
event that the edges of `S` are monochromatic with prescribed colours `φ : S → [p]` is a
cylinder event of probability `p^{-rℓ}`. Summing over injective `φ` (resp. `φ` with values in a
set `U`) gives the expectation of the weight of tuples whose edges lie in distinct parts
(resp. in parts from `U`); both are concentrated.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}

/-- The edges of `S` are monochromatic, the edge `e` having colour `φ e`. -/
def colEv (S : Finset (Finset V)) (φ : {e // e ∈ S} → Fin p) (τ : V → Fin p) : Prop :=
  ∀ e : {e // e ∈ S}, ∀ v ∈ e.1, τ v = φ e

theorem pProb_colEv (hp : 0 < p) (S : Finset (Finset V))
    (hS : ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint e g) (φ : {e // e ∈ S} → Fin p) :
    pProb (unif V p) (colEv S φ) = (1 / (p : ℝ)) ^ (S.biUnion id).card := by
  classical
  set x : V → Fin p := fun v => if h : ∃ e ∈ S, v ∈ e then φ ⟨h.choose, h.choose_spec.1⟩
    else ⟨0, hp⟩ with hx
  have hxv : ∀ e (he : e ∈ S), ∀ v ∈ e, x v = φ ⟨e, he⟩ := by
    intro e he v hv
    have h : ∃ e ∈ S, v ∈ e := ⟨e, he, hv⟩
    simp only [hx, dif_pos h]
    have heq : h.choose = e := by
      by_contra hne
      have := hS _ h.choose_spec.1 e he hne
      exact Finset.disjoint_left.mp this h.choose_spec.2 hv
    congr 1
    exact Subtype.ext heq
  have hiff : ∀ τ, colEv S φ τ ↔ ∀ v ∈ S.biUnion id, τ v = x v := by
    intro τ
    constructor
    · intro h v hv
      obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
      rw [hxv e he v hve]
      exact h ⟨e, he⟩ v hve
    · intro h e v hv
      rw [h v (mem_biUnion.mpr ⟨e.1, e.2, hv⟩), hxv e.1 e.2 v hv]
  rw [pProb_congr hiff, pProb_cylinder (unif_isPMF p hp)]
  simp [unif, prod_const]

theorem colEv_unique (S : Finset (Finset V)) (hne : ∀ e ∈ S, e.Nonempty)
    {φ φ' : {e // e ∈ S} → Fin p} {τ : V → Fin p} (h : colEv S φ τ) (h' : colEv S φ' τ) :
    φ = φ' := by
  funext e
  obtain ⟨v, hv⟩ := hne e.1 e.2
  rw [← h e v hv, ← h' e v hv]

theorem pProb_exists_colEv (hp : 0 < p) (S : Finset (Finset V))
    (hS : ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint e g) (hne : ∀ e ∈ S, e.Nonempty)
    (Φ : Finset ({e // e ∈ S} → Fin p)) :
    pProb (unif V p) (fun τ => ∃ φ ∈ Φ, colEv S φ τ) =
      Φ.card * (1 / (p : ℝ)) ^ (S.biUnion id).card := by
  classical
  have hpt : ∀ τ, (if ∃ φ ∈ Φ, colEv S φ τ then (1 : ℝ) else 0) =
      ∑ φ ∈ Φ, if colEv S φ τ then 1 else 0 := by
    intro τ
    by_cases h : ∃ φ ∈ Φ, colEv S φ τ
    · obtain ⟨φ₀, hφ₀, h₀⟩ := h
      rw [if_pos ⟨φ₀, hφ₀, h₀⟩, sum_eq_single φ₀ (fun φ _ hφ => ?_) (fun h => absurd hφ₀ h),
        if_pos h₀]
      rw [if_neg]
      intro hc
      exact hφ (colEv_unique S hne hc h₀)
    · rw [if_neg h]
      refine (sum_eq_zero fun φ hφ => ?_).symm
      rw [if_neg]
      exact fun hc => h ⟨φ, hφ, hc⟩
  rw [show pProb (unif V p) (fun τ => ∃ φ ∈ Φ, colEv S φ τ) = pE (unif V p)
      (fun τ => ∑ φ ∈ Φ, if colEv S φ τ then (1 : ℝ) else 0) from by
    unfold pProb; congr 1; funext τ; convert hpt τ]
  rw [pE_sum]
  have : ∀ φ ∈ Φ, pE (unif V p) (fun τ => if colEv S φ τ then (1 : ℝ) else 0) =
      (1 / (p : ℝ)) ^ (S.biUnion id).card := by
    intro φ _
    rw [← pProb_colEv hp S hS φ]
    unfold pProb
    congr 1
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]

omit [Fintype V] in
theorem colEv_local (S : Finset (Finset V)) (Φ : Finset ({e // e ∈ S} → Fin p))
    (τ τ' : V → Fin p) (h : ∀ v ∈ S.biUnion id, τ v = τ' v) :
    (∃ φ ∈ Φ, colEv S φ τ) ↔ (∃ φ ∈ Φ, colEv S φ τ') := by
  have key : ∀ φ, colEv S φ τ ↔ colEv S φ τ' := by
    intro φ
    constructor
    · intro hc e v hv
      rw [← h v (mem_biUnion.mpr ⟨e.1, e.2, hv⟩)]
      exact hc e v hv
    · intro hc e v hv
      rw [h v (mem_biUnion.mpr ⟨e.1, e.2, hv⟩)]
      exact hc e v hv
  simp_rw [key]

/-! ## The two families of colour assignments -/

theorem distinctParts_iff (H : Finset (Finset V)) (τ : V → Fin p) (S : Finset (Finset V))
    (hSH : S ⊆ H) (hne : ∀ e ∈ S, e.Nonempty) :
    DistinctParts (part H τ) S ↔
      ∃ φ ∈ (univ.filter (fun φ : {e // e ∈ S} → Fin p => Function.Injective φ)),
        colEv S φ τ := by
  classical
  constructor
  · rintro ⟨hin, huniq⟩
    choose φ hφ using fun e : {e // e ∈ S} => hin e.1 e.2
    refine ⟨φ, mem_filter.mpr ⟨mem_univ _, fun e e' hee => ?_⟩, fun e v hv => ?_⟩
    · have h1 := hφ e
      have h2 := hφ e'
      rw [hee] at h1
      exact Subtype.ext (huniq e.1 e.2 e'.1 e'.2 _ h1 h2)
    · exact (mem_filter.mp (hφ e)).2 v hv
  · rintro ⟨φ, hφ, hc⟩
    have hinj := (mem_filter.mp hφ).2
    refine ⟨fun e he => ⟨φ ⟨e, he⟩, mem_filter.mpr ⟨hSH he, fun v hv => hc ⟨e, he⟩ v hv⟩⟩,
      fun e he e' he' i hi hi' => ?_⟩
    have hcol : ∀ g (hg : g ∈ S), g ∈ part H τ i → φ ⟨g, hg⟩ = i := by
      intro g hg hgi
      obtain ⟨v, hv⟩ := hne g hg
      rw [← hc ⟨g, hg⟩ v hv]
      exact (mem_filter.mp hgi).2 v hv
    have := hinj ((hcol e he hi).trans (hcol e' he' hi').symm)
    exact congrArg Subtype.val this

theorem inRange_iff {ℓ : ℕ} (H : Finset (Finset V)) (τ : V → Fin p) (u : Fin ℓ → Fin p)
    (S : Finset (Finset V)) (hSH : S ⊆ H) :
    (∀ e ∈ S, ∃ m, e ∈ part H τ (u m)) ↔
      ∃ φ ∈ (univ.filter (fun φ : {e // e ∈ S} → Fin p => ∀ e, ∃ m, φ e = u m)),
        colEv S φ τ := by
  classical
  constructor
  · intro h
    choose m hm using fun e : {e // e ∈ S} => h e.1 e.2
    exact ⟨fun e => u (m e), mem_filter.mpr ⟨mem_univ _, fun e => ⟨m e, rfl⟩⟩,
      fun e v hv => (mem_filter.mp (hm e)).2 v hv⟩
  · rintro ⟨φ, hφ, hc⟩ e he
    obtain ⟨m, hm⟩ := (mem_filter.mp hφ).2 ⟨e, he⟩
    exact ⟨m, mem_filter.mpr ⟨hSH he, fun v hv => (hc ⟨e, he⟩ v hv).trans hm⟩⟩

omit [Fintype V] in
theorem card_injective_filter (S : Finset (Finset V)) :
    (univ.filter (fun φ : {e // e ∈ S} → Fin p => Function.Injective φ)).card =
      p.descFactorial S.card := by
  classical
  rw [← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding {e // e ∈ S} (Fin p)),
    Fintype.card_embedding_eq]
  simp

omit [Fintype V] in
theorem card_inRange_filter {ℓ : ℕ} (S : Finset (Finset V)) (u : Fin ℓ → Fin p) :
    (univ.filter (fun φ : {e // e ∈ S} → Fin p => ∀ e, ∃ m, φ e = u m)).card ≤
      ℓ ^ S.card := by
  classical
  have hsub : univ.filter (fun φ : {e // e ∈ S} → Fin p => ∀ e, ∃ m, φ e = u m) ⊆
      (univ : Finset ({e // e ∈ S} → Fin ℓ)).image (fun m => u ∘ m) := by
    intro φ hφ
    choose m hm using (mem_filter.mp hφ).2
    exact mem_image.mpr ⟨m, mem_univ _, funext fun e => (hm e).symm⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

/-! ## Expectations and concentration -/

/-- The weighted sum of tuples coloured according to some `φ ∈ Φ S`. -/
noncomputable def colSum (ℓ : ℕ) (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (Φ : (S : Finset (Finset V)) → Finset ({e // e ∈ S} → Fin p)) (τ : V → Fin p) : ℝ :=
  open Classical in
  ∑ S ∈ H.powersetCard ℓ, ω S * if ∃ φ ∈ Φ S, colEv S φ τ then 1 else 0

omit [Fintype V] in
theorem biUnion_card_of_matching {r : ℕ} (S : Finset (Finset V)) (huni : IsUniform S r)
    (hm : IsMatching S) : (S.biUnion id).card = r * S.card := by
  show (S.biUnion fun e => e).card = _
  rw [card_biUnion (fun e he g hg heg => hm e he g hg heg)]
  rw [sum_congr rfl fun e he => huni e he, sum_const, smul_eq_mul, mul_comm]

theorem pE_colSum (hp : 0 < p) (ℓ r : ℕ) (hr : 1 ≤ r) (H : Finset (Finset V))
    (huni : IsUniform H r) (ω : Finset (Finset V) → ℝ)
    (hclean : ∀ S ∈ H.powersetCard ℓ, ω S ≠ 0 → IsMatching S)
    (Φ : (S : Finset (Finset V)) → Finset ({e // e ∈ S} → Fin p)) :
    pE (unif V p) (colSum ℓ H ω Φ) =
      ∑ S ∈ H.powersetCard ℓ, ω S * ((Φ S).card * (1 / (p : ℝ)) ^ (r * ℓ)) := by
  classical
  unfold colSum
  rw [pE_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [pE_const_mul]
  by_cases hω : ω S = 0
  · rw [hω, zero_mul, zero_mul]
  have hm := hclean S hS hω
  obtain ⟨hSH, hSc⟩ := mem_powersetCard.mp hS
  have hne : ∀ e ∈ S, e.Nonempty := fun e he => by
    rw [← card_pos, huni e (hSH he)]; omega
  have h := pProb_exists_colEv hp S hm hne (Φ S)
  rw [biUnion_card_of_matching S (fun e he => huni e (hSH he)) hm, hSc] at h
  rw [← h]
  unfold pProb
  congr 2
  funext τ
  split_ifs <;> rfl

/-- The influence of a vertex on a tuple sum. -/
theorem cylGap_tuple_le (ℓ : ℕ) (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) (Δ m : ℝ) (hm : 0 ≤ m)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hη : ∀ e ∈ H, tdeg ℓ ω H {e} ≤ m) (x : V) :
    cylGap (ι := V) (H.powersetCard ℓ) ω (fun S => S.biUnion id) x ≤ Δ * m := by
  classical
  unfold cylGap
  have h1 : ∑ S ∈ (H.powersetCard ℓ).filter (fun S => x ∈ S.biUnion id), ω S ≤
      ∑ S ∈ H.powersetCard ℓ, ω S * ((S.filter (fun e => x ∈ e)).card : ℝ) := by
    rw [sum_filter]
    refine sum_le_sum fun S hS => ?_
    split_ifs with hx
    · obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
      have : (1 : ℝ) ≤ (S.filter (fun e => x ∈ e)).card := by
        exact_mod_cast card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hxe⟩⟩
      nlinarith [hω0 S hS]
    · exact mul_nonneg (hω0 S hS) (Nat.cast_nonneg _)
  have h2 : ∑ S ∈ H.powersetCard ℓ, ω S * ((S.filter (fun e => x ∈ e)).card : ℝ) =
      ∑ e ∈ H.filter (fun e => x ∈ e), tdeg ℓ ω H {e} := by
    unfold tdeg
    simp_rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum, mul_one]
    rw [sum_comm' (t' := H.filter (fun e => x ∈ e))
      (s' := fun e => (H.powersetCard ℓ).filter (fun S => {e} ⊆ S))]
    intro S e
    simp only [mem_filter, mem_powersetCard, singleton_subset_iff]
    constructor
    · rintro ⟨⟨hSH, hSc⟩, he, hx⟩
      exact ⟨⟨⟨hSH, hSc⟩, he⟩, hSH he, hx⟩
    · rintro ⟨⟨⟨hSH, hSc⟩, he⟩, _, hx⟩
      exact ⟨⟨hSH, hSc⟩, he, hx⟩
  have h3 : ∑ e ∈ H.filter (fun e => x ∈ e), tdeg ℓ ω H {e} ≤ (degree H x : ℝ) * m := by
    calc _ ≤ ∑ e ∈ H.filter (fun e => x ∈ e), m :=
          sum_le_sum fun e he => hη e (mem_filter.mp he).1
      _ = _ := by rw [sum_const, nsmul_eq_mul]; rfl
  have h4 : (degree H x : ℝ) * m ≤ Δ * m := mul_le_mul_of_nonneg_right (hdeg x) hm
  linarith

theorem sum_card_biUnion_le (ℓ r : ℕ) (H : Finset (Finset V)) (huni : IsUniform H r)
    (ω : Finset (Finset V) → ℝ) (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S) :
    ∑ S ∈ H.powersetCard ℓ, ω S * ((S.biUnion id).card : ℝ) ≤ (r * ℓ) * tweight ℓ ω H := by
  unfold tweight
  rw [mul_sum]
  refine sum_le_sum fun S hS => ?_
  obtain ⟨hSH, hSc⟩ := mem_powersetCard.mp hS
  have : ((S.biUnion id).card : ℝ) ≤ r * ℓ := by
    have h1 : (S.biUnion id).card ≤ ∑ e ∈ S, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ S, (id e).card = r * ℓ := by
      simp only [id]
      rw [sum_congr rfl fun e he => huni e (hSH he), sum_const, smul_eq_mul, hSc, mul_comm]
    exact_mod_cast h2 ▸ h1
  rw [mul_comm ((r : ℝ) * ℓ)]
  exact mul_le_mul_of_nonneg_left this (hω0 S hS)

/-- Concentration of tuple colour sums. -/
theorem colSum_tail (hp : 0 < p) (ℓ r : ℕ) (H : Finset (Finset V)) (huni : IsUniform H r)
    (ω : Finset (Finset V) → ℝ) (hω0 : ∀ S ∈ H.powersetCard ℓ, 0 ≤ ω S)
    (Φ : (S : Finset (Finset V)) → Finset ({e // e ∈ S} → Fin p))
    (Δ η : ℝ) (hΔ : 0 < Δ) (hη : 0 < η) (hpos : 0 < tweight ℓ ω H)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hηb : ∀ e ∈ H, tdeg ℓ ω H {e} ≤ η * tweight ℓ ω H)
    (s : ℝ) (hs : 0 < s) :
    pProb (unif V p) (fun τ => s * tweight ℓ ω H ≤
        colSum ℓ H ω Φ τ - pE (unif V p) (colSum ℓ H ω Φ)) ≤
      Real.exp (-(s ^ 2 / (2 * Δ * η * (r * ℓ + s)))) ∧
    pProb (unif V p) (fun τ => s * tweight ℓ ω H ≤
        pE (unif V p) (colSum ℓ H ω Φ) - colSum ℓ H ω Φ τ) ≤
      Real.exp (-(s ^ 2 / (2 * Δ * η * (r * ℓ + s)))) := by
  classical
  set W := tweight ℓ ω H with hW
  have hL0 : 0 < Δ * (η * W) := by positivity
  have h := local_tail (unif V p) (unif_isPMF p hp) (H.powersetCard ℓ) ω hω0
    (fun S => S.biUnion id)
    (fun S τ => if ∃ φ ∈ Φ S, colEv S φ τ then (1 : ℝ) else 0)
    (fun S τ => by split_ifs <;> norm_num)
    (fun S τ τ' hττ => by simp only [colEv_local S (Φ S) τ τ' hττ])
    (Δ * (η * W)) ((r * ℓ) * W) hL0
    (cylGap_tuple_le ℓ H ω hω0 Δ (η * W) (by positivity) hdeg hηb)
    (sum_card_biUnion_le ℓ r H huni ω hω0) (s * W) (by positivity)
  have heq : (s * W) ^ 2 / (2 * (Δ * (η * W) * (r * ℓ * W) + Δ * (η * W) * (s * W))) =
      s ^ 2 / (2 * Δ * η * (r * ℓ + s)) := by
    field_simp
  rw [heq] at h
  exact h


/-! ## The bad events of Step 1 -/

open Classical in
/-- Weight of the `ℓ`-sets of edges lying in pairwise distinct parts. -/
noncomputable def dSum (ℓ : ℕ) (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (τ : V → Fin p) : ℝ :=
  ∑ S ∈ H.powersetCard ℓ, ω S * if DistinctParts (part H τ) S then 1 else 0

open Classical in
/-- Weight of the `ℓ`-sets of edges lying in parts from the range of `u`. -/
noncomputable def ySum {ℓ : ℕ} (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ)
    (u : Fin ℓ → Fin p) (τ : V → Fin p) : ℝ :=
  ∑ S ∈ H.powersetCard ℓ, ω S * if ∀ e ∈ S, ∃ m, e ∈ part H τ (u m) then 1 else 0

theorem dSum_eq (ℓ r : ℕ) (hr : 1 ≤ r) (H : Finset (Finset V)) (huni : IsUniform H r)
    (ω : Finset (Finset V) → ℝ) :
    dSum ℓ H ω = colSum ℓ H ω
      (fun S => univ.filter (fun φ : {e // e ∈ S} → Fin p => Function.Injective φ)) := by
  classical
  funext τ
  unfold dSum colSum
  refine sum_congr rfl fun S hS => ?_
  obtain ⟨hSH, -⟩ := mem_powersetCard.mp hS
  have hne : ∀ e ∈ S, e.Nonempty := fun e he => by
    rw [← card_pos, huni e (hSH he)]; omega
  congr 1
  simp only [distinctParts_iff H τ S hSH hne]

theorem ySum_eq {ℓ : ℕ} (H : Finset (Finset V)) (ω : Finset (Finset V) → ℝ) (u : Fin ℓ → Fin p) :
    ySum H ω u = colSum ℓ H ω
      (fun S => univ.filter (fun φ : {e // e ∈ S} → Fin p => ∀ e, ∃ m, φ e = u m)) := by
  classical
  funext τ
  unfold ySum colSum
  refine sum_congr rfl fun S hS => ?_
  obtain ⟨hSH, -⟩ := mem_powersetCard.mp hS
  congr 1
  simp only [inRange_iff H τ u S hSH]

/-- **Step 1 for tuple weights**: the probability that some tuple sum is not concentrated. -/
theorem tuple_vertex_bad (hp : 0 < p) (r : ℕ) (hr : 1 ≤ r) (H : Finset (Finset V))
    (huni : IsUniform H r) (Δ η ξ : ℝ) (hΔ : 0 < Δ) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) {κ : Type*} (K : Finset κ) (ℓ : κ → ℕ)
    (W : κ → Finset (Finset V) → ℝ) (hW0 : ∀ k ∈ K, ∀ S ∈ H.powersetCard (ℓ k), 0 ≤ W k S)
    (hclean : ∀ k ∈ K, ∀ S ∈ H.powersetCard (ℓ k), W k S ≠ 0 → IsMatching S)
    (hpos : ∀ k ∈ K, 0 < tweight (ℓ k) (W k) H)
    (hηb : ∀ k ∈ K, ∀ e ∈ H, tdeg (ℓ k) (W k) H {e} ≤ η * tweight (ℓ k) (W k) H)
    (hℓp : ∀ k ∈ K, ℓ k ≤ p) :
    pProb (unif V p) (fun τ => ∃ k ∈ K,
      ¬ (|dSum (ℓ k) H (W k) τ - tweight (ℓ k) (W k) H * (p.descFactorial (ℓ k) *
          (1 / (p : ℝ)) ^ (r * ℓ k))| ≤
        ξ * (tweight (ℓ k) (W k) H * (p.descFactorial (ℓ k) * (1 / (p : ℝ)) ^ (r * ℓ k)))) ∨
      ∃ u : Fin (ℓ k) → Fin p, ¬ (ySum H (W k) u τ ≤
        2 * ((ℓ k : ℝ) ^ ℓ k * (1 / (p : ℝ)) ^ (r * ℓ k)) * tweight (ℓ k) (W k) H)) ≤
    ∑ k ∈ K, (2 * Real.exp (-((ξ * (p.descFactorial (ℓ k) * (1 / (p : ℝ)) ^ (r * ℓ k))) ^ 2 /
        (2 * Δ * η * (r * ℓ k + ξ * (p.descFactorial (ℓ k) * (1 / (p : ℝ)) ^ (r * ℓ k)))))) +
      (p : ℝ) ^ ℓ k * Real.exp (-(((ℓ k : ℝ) ^ ℓ k * (1 / (p : ℝ)) ^ (r * ℓ k)) ^ 2 /
        (2 * Δ * η * (r * ℓ k + (ℓ k : ℝ) ^ ℓ k * (1 / (p : ℝ)) ^ (r * ℓ k)))))) := by
  classical
  have hP := unif_isPMF (ι := V) p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  refine (pProb_exists_le hP _ _).trans (sum_le_sum fun k hk => ?_)
  set ℓk := ℓ k
  set tw := tweight ℓk (W k) H with htw
  set ρ : ℝ := (1 / (p : ℝ)) ^ (r * ℓk) with hρ
  have hρ0 : 0 < ρ := by positivity
  have htw0 := hpos k hk
  have hdF : (0 : ℝ) < p.descFactorial ℓk := by
    exact_mod_cast Nat.descFactorial_pos.mpr (hℓp k hk)
  -- distinct parts
  set ΦD := fun S : Finset (Finset V) =>
    univ.filter (fun φ : {e // e ∈ S} → Fin p => Function.Injective φ) with hΦD
  have hED : pE (unif V p) (colSum ℓk H (W k) ΦD) = tw * (p.descFactorial ℓk * ρ) := by
    rw [pE_colSum hp ℓk r hr H huni (W k) (hclean k hk), htw, tweight, sum_mul]
    refine sum_congr rfl fun S hS => ?_
    rw [hΦD]; dsimp only
    rw [card_injective_filter, (mem_powersetCard.mp hS).2]
  have hD := colSum_tail hp ℓk r H huni (W k) (hW0 k hk) ΦD Δ η hΔ hη htw0 hdeg (hηb k hk)
    (ξ * (p.descFactorial ℓk * ρ)) (by positivity)
  rw [hED] at hD
  -- parts in a range
  have hY : ∀ u : Fin ℓk → Fin p, pProb (unif V p) (fun τ => ¬ (ySum H (W k) u τ ≤
      2 * ((ℓk : ℝ) ^ ℓk * ρ) * tw)) ≤ Real.exp (-(((ℓk : ℝ) ^ ℓk * ρ) ^ 2 /
        (2 * Δ * η * (r * ℓk + (ℓk : ℝ) ^ ℓk * ρ)))) := by
    intro u
    set ΦY := fun S : Finset (Finset V) =>
      univ.filter (fun φ : {e // e ∈ S} → Fin p => ∀ e, ∃ m, φ e = u m) with hΦY
    have hEY : pE (unif V p) (colSum ℓk H (W k) ΦY) ≤ tw * ((ℓk : ℝ) ^ ℓk * ρ) := by
      rw [pE_colSum hp ℓk r hr H huni (W k) (hclean k hk), htw, tweight, sum_mul]
      refine sum_le_sum fun S hS => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hW0 k hk S hS)
      refine mul_le_mul_of_nonneg_right ?_ hρ0.le
      rw [hΦY]; dsimp only
      have := card_inRange_filter S u
      rw [(mem_powersetCard.mp hS).2] at this
      exact_mod_cast this
    have hl1 : (0 : ℝ) < (ℓk : ℝ) ^ ℓk := by
      rcases Nat.eq_zero_or_pos ℓk with h | h
      · rw [h]; simp
      · have : (0 : ℝ) < ℓk := by exact_mod_cast h
        positivity
    have hT := (colSum_tail hp ℓk r H huni (W k) (hW0 k hk) ΦY Δ η hΔ hη htw0 hdeg (hηb k hk)
      ((ℓk : ℝ) ^ ℓk * ρ) (by positivity)).1
    refine le_trans (pProb_mono hP fun τ hτ => ?_) hT
    push_neg at hτ
    rw [ySum_eq] at hτ
    linarith
  have hYall := (pProb_exists_le hP (univ : Finset (Fin ℓk → Fin p)) (fun u τ =>
      ¬ (ySum H (W k) u τ ≤ 2 * ((ℓk : ℝ) ^ ℓk * ρ) * tw))).trans
    (sum_le_sum fun u _ => hY u)
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul] at hYall
  push_cast at hYall
  have hor := pProb_or_le hP (fun τ => ¬ (|dSum ℓk H (W k) τ - tw * (p.descFactorial ℓk * ρ)| ≤
      ξ * (tw * (p.descFactorial ℓk * ρ))))
    (fun τ => ∃ u : Fin ℓk → Fin p, ¬ (ySum H (W k) u τ ≤ 2 * ((ℓk : ℝ) ^ ℓk * ρ) * tw))
  have hDb : pProb (unif V p) (fun τ => ¬ (|dSum ℓk H (W k) τ - tw * (p.descFactorial ℓk * ρ)| ≤
      ξ * (tw * (p.descFactorial ℓk * ρ)))) ≤
      2 * Real.exp (-((ξ * (p.descFactorial ℓk * ρ)) ^ 2 /
        (2 * Δ * η * (r * ℓk + ξ * (p.descFactorial ℓk * ρ))))) := by
    have h2 := pProb_or_le hP (fun τ => ξ * (p.descFactorial ℓk * ρ) * tw ≤
        colSum ℓk H (W k) ΦD τ - tw * (p.descFactorial ℓk * ρ))
      (fun τ => ξ * (p.descFactorial ℓk * ρ) * tw ≤
        tw * (p.descFactorial ℓk * ρ) - colSum ℓk H (W k) ΦD τ)
    refine le_trans (pProb_mono hP fun τ hτ => ?_) (h2.trans (by linarith [hD.1, hD.2]))
    rw [dSum_eq ℓk r hr H huni] at hτ
    rw [abs_le] at hτ
    push_neg at hτ
    by_cases h : -(ξ * (tw * (p.descFactorial ℓk * ρ))) ≤
        colSum ℓk H (W k) ΦD τ - tw * (p.descFactorial ℓk * ρ)
    · left; have := hτ h; linarith
    · right; push_neg at h; linarith
  have hY2 : pProb (unif V p) (fun τ => ∃ u : Fin ℓk → Fin p,
      ¬ (ySum H (W k) u τ ≤ 2 * ((ℓk : ℝ) ^ ℓk * ρ) * tw)) ≤ (p : ℝ) ^ ℓk *
        Real.exp (-(((ℓk : ℝ) ^ ℓk * ρ) ^ 2 / (2 * Δ * η * (r * ℓk + (ℓk : ℝ) ^ ℓk * ρ)))) :=
    le_trans (pProb_mono hP fun τ ⟨u, hu⟩ => ⟨u, mem_univ _, hu⟩) hYall
  exact hor.trans (by linarith)

end Pseudorandom
