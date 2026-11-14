/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.SpectrumMain
public import CountingCone.VanDerWaerden.Full
public import CountingCone.LL.STSMain

/-!
# Completion of sparse packings and counting (`k` classes), part 1

* `kBlocks lab`, `kCount lab`: the Steiner triple systems on `Fin n` all of whose blocks meet
  exactly two classes of `lab`; `kCount_upper` (Linial–Luria, Palomar PALOMAR-2026-10-22-000017).
* `mem_kBlocks_of_decomp`: an allowed decomposition of the complete host is such a system.
* `union_decomp`: a packing of allowed triangles plus a decomposition of the residual host is a
  decomposition of the complete host.
* **`kbicolour_completion`**: for `k ≥ 3`, every large admissible labelling with classes `≥ δ n`
  and seed data, and every packing of bicoloured triangles whose leave has maximum degree
  `≤ γ n`, extends to a `k`-bicoloured STS (Theorem T on `K_n − L`, residual seed, H2–H4).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {k n : ℕ}

open Classical in
/-- Block sets of the `k`-bicoloured Steiner triple systems on `Fin n`. -/
def kBlocks (lab : Fin n → Fin k) : Finset (Finset (Finset (Fin n))) :=
  univ.filter fun X => _root_.STS.IsSTS X ∧ ∀ B ∈ X, (B.image lab).card = 2

/-- **Number of `k`-bicoloured Steiner triple systems with class partition `lab`.** -/
def kCount (lab : Fin n → Fin k) : ℕ := #(kBlocks lab)

theorem kCount_le (lab : Fin n → Fin k) : kCount lab ≤ _root_.STS.D n := by
  classical
  unfold kCount _root_.STS.D
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_le_card fun X hX => by
    simp only [kBlocks, mem_filter, mem_univ, true_and] at hX ⊢; exact hX.1

/-- **Upper bound** (Linial–Luria, explicit). -/
theorem kCount_upper (lab : Fin n → Fin k) (hn : 4 ≤ n) :
    (kCount lab : ℝ) ≤ Real.exp ((n * (n - 1) / 6 : ℝ) *
      (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3))) :=
  (Nat.cast_le.mpr (kCount_le lab)).trans (LinialLuria.sts_upper_bound_explicit n hn)

theorem card_sts_le_sq {X : Finset (Finset (Fin n))} (hX : _root_.STS.IsSTS X) : #X ≤ n ^ 2 := by
  classical
  have hpair : ∀ B ∈ X, ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ p.1 ∈ B ∧ p.2 ∈ B := by
    intro B hB
    obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp (hX.1 B hB)
    exact ⟨(x, y), hxy, by simp, by simp⟩
  rcases X.eq_empty_or_nonempty with rfl | ⟨B₀, hB₀⟩
  · simp
  obtain ⟨x₀, -⟩ := card_pos.mp (by rw [hX.1 B₀ hB₀]; norm_num : 0 < B₀.card)
  haveI : Nonempty (Fin n × Fin n) := ⟨(x₀, x₀)⟩
  choose! f hf using hpair
  have hinj : Set.InjOn f X := by
    intro B hB B' hB' he
    obtain ⟨h1, h2, h3⟩ := hf B hB
    obtain ⟨-, h2', h3'⟩ := hf B' hB'
    rw [he] at h2 h3
    obtain ⟨C, -, hC⟩ := hX.2 _ _ (he ▸ h1)
    exact (hC B ⟨hB, he ▸ h2, he ▸ h3⟩).trans (hC B' ⟨hB', h2', h3'⟩).symm
  calc #X = #(X.image f) := (card_image_of_injOn hinj).symm
    _ ≤ #(univ : Finset (Fin n × Fin n)) := card_le_univ _
    _ = n ^ 2 := by simp [sq]

theorem mem_kBlocks_of_decomp (lab : Fin n → Fin k) {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D) : D ∈ kBlocks lab := by
  classical
  obtain ⟨hall, hdisj, hcov⟩ := hD
  have hmem : ∀ T ∈ D, ∀ x y, x ≠ y → (s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T) := by
    intro T _ x y hxy
    simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, hxy]
  unfold kBlocks
  rw [mem_filter]
  refine ⟨mem_univ _, ⟨fun T hT => (hall T hT).1, fun x y hxy => ?_⟩, fun T hT => ?_⟩
  · have he : s(x, y) ∈ edges (kHost lab) := by simp [edges, kHost, hxy]
    have he' := (Finset.ext_iff.1 hcov s(x, y)).2 he
    simp only [Finset.mem_biUnion] at he'
    obtain ⟨T, hT, hxyT⟩ := he'
    refine ⟨T, ⟨hT, (hmem T hT x y hxy).1 hxyT⟩, ?_⟩
    rintro T' ⟨hT', hx', hy'⟩
    by_contra hne
    have := hdisj hT' hT hne
    exact disjoint_left.1 this ((hmem T' hT' x y hxy).2 ⟨hx', hy'⟩) hxyT
  · have h := (hall T hT).2.2
    exact h.2

/-- A packing plus a decomposition of the residual host. -/
theorem union_decomp (lab : Fin n → Fin k) {P : Finset (Finset (Fin n))}
    (hPall : ∀ T ∈ P, IsAllowed (kHost lab) (bicF k) T)
    (hPd : (P : Set (Finset (Fin n))).PairwiseDisjoint triEdges) {D : Finset (Finset (Fin n))}
    (hD : IsDecomposition (rHostK lab (P.biUnion triEdges)) (bicF k)
      (edges (rHostK lab (P.biUnion triEdges))) D) :
    IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) (D ∪ P) := by
  classical
  set L := P.biUnion triEdges with hL
  have hDdisj : ∀ T ∈ D, Disjoint (triEdges T) L := fun T hT => disj_of_rHostK lab (hD.1 T hT)
  have hPsub : ∀ T ∈ P, triEdges T ⊆ L := fun T hT e he => mem_biUnion.2 ⟨T, hT, he⟩
  refine ⟨fun T hT => ?_, fun T hT T' hT' hne => ?_, ?_⟩
  · rcases mem_union.1 hT with h | h
    · exact allowed_kHost_of_rHostK lab (hD.1 T h)
    · exact hPall T h
  · simp only [coe_union, Set.mem_union, mem_coe] at hT hT'
    rcases hT with h | h <;> rcases hT' with h' | h'
    · exact hD.2.1 h h' hne
    · show Disjoint (triEdges T) (triEdges T')
      exact (hDdisj T h).mono_right (hPsub T' h')
    · show Disjoint (triEdges T) (triEdges T')
      exact ((hDdisj T' h').mono_right (hPsub T h)).symm
    · exact hPd h h' hne
  · ext e
    have hDe := Finset.ext_iff.1 hD.2.2 e
    simp only [Finset.mem_biUnion, mem_union] at hDe ⊢
    constructor
    · rintro ⟨T, hT | hT, he⟩
      · have := hDe.1 ⟨T, hT, he⟩
        have h1 : e ∈ (rG L).edgeSet := by simpa [edges] using this
        simp only [edges, mem_filter, mem_univ, true_and]
        exact SimpleGraph.edgeSet_mono le_top h1
      · induction e using Sym2.ind with
        | _ u v =>
        simp only [edges, mem_filter, mem_univ, true_and, kHost, SimpleGraph.top_adj,
          SimpleGraph.mem_edgeSet]
        simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
        exact he.2
    · intro he
      by_cases heL : e ∈ L
      · rw [hL, mem_biUnion] at heL
        obtain ⟨T, hT, he'⟩ := heL
        exact ⟨T, Or.inr hT, he'⟩
      · obtain ⟨T, hT, he'⟩ := hDe.2 (by
          induction e using Sym2.ind with
          | _ u v =>
          simp only [edges, mem_filter, mem_univ, true_and, SimpleGraph.top_adj,
            SimpleGraph.mem_edgeSet, rG_adj] at he ⊢
          exact ⟨heL, he⟩)
        exact ⟨T, Or.inl hT, he'⟩

set_option maxHeartbeats 4000000 in
/-- **Completion of sparse packings (`k` classes).** -/
theorem kbicolour_completion (k : ℕ) (hk : 3 ≤ k) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ δ / 20 ∧ ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      (∃ a, SeedData (ksz lab) η a) →
      ∀ (P : Finset (Finset (Fin n))) (Δ : ℕ),
        (∀ T ∈ P, IsAllowed (kHost lab) (bicF k) T) →
        (P : Set (Finset (Fin n))).PairwiseDisjoint triEdges →
        (∀ p, degL (P.biUnion triEdges) p ≤ Δ) → (Δ : ℝ) ≤ γ * n →
        ∃ D, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧ P ⊆ D := by
  classical
  set o : Fin k := ⟨0, by omega⟩ with ho
  set R : ℝ := 2 / δ with hR
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hδ]; linarith
  set C₀ : ℝ := 1 / η + 2 / δ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 2 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 0 < 1 / η := by positivity
    linarith
  set Kc : ℝ := (#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set B : ℝ := 1 + 8 * Kc * C₀ ^ 2 + 20 / δ + 2 * ((k : ℝ) + 4) / δ with hB
  have tB1 : 0 ≤ 8 * Kc * C₀ ^ 2 := by positivity
  have tB2 : 0 ≤ 20 / δ := by positivity
  have tB3 : 0 ≤ 2 * ((k : ℝ) + 4) / δ := by positivity
  have hBpos : 0 < B := by linarith
  set γ : ℝ := 1 / B with hγ
  have hγ0 : 0 < γ := by positivity
  set lam : ℝ := γ / 18 with hlam
  have hlam0 : 0 < lam := by positivity
  have G1 : 8 * Kc * C₀ ^ 2 * γ ≤ 1 := le_of_mul_inv hBpos hγ (by linarith)
  have G2 : 20 * γ ≤ δ := by
    have := le_of_mul_inv hBpos hγ (show 20 / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have G3 : 2 * ((k : ℝ) + 4) * γ ≤ δ := by
    have := le_of_mul_inv hBpos hγ (show 2 * ((k : ℝ) + 4) / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have L1 : 144 * Kc * C₀ ^ 2 * lam ≤ 1 := by rw [hlam]; linarith
  have L5 : 360 * lam ≤ δ := by rw [hlam]; linarith
  have L6 : 36 * ((k : ℝ) + 4) * lam ≤ δ := by rw [hlam]; linarith
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T (bicF k) (δ ^ 2 / 4) (2 * C₀) 6 (by positivity)
    (by linarith) le_rfl
  set N₁ : ℝ := (513 + 64 * R ^ 3) / δ + 20 / δ + 2 * ((k : ℝ) + 4) / δ + k + 1 with hN₁
  have u1 : 0 ≤ (513 + 64 * R ^ 3) / δ := by positivity
  have u6 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨γ, hγ0, by linarith, max nT ⌈N₁⌉₊, fun n lab hn hodd hcls heven hdiv ⟨a, ha⟩ P Δ hPall
    hPd hdeg hΔγ => ?_⟩
  have hnN : N₁ ≤ n := Nat.ceil_le.1 (le_of_max_le_right hn)
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hδn : 513 + 64 * R ^ 3 ≤ δ * n := by
    have h : (513 + 64 * R ^ 3) / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hδn20 : 20 ≤ δ * n := by
    have h : 20 / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hδnk : 2 * ((k : ℝ) + 4) < δ * n := by
    have h : 2 * ((k : ℝ) + 4) / δ < n := by linarith
    rw [div_lt_iff₀ hδ] at h; linarith
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have hcls' : ∀ X, δ * Fintype.card (Fin n) ≤ ksz lab X := by
    intro X; rw [hcard]; exact hcls X
  have hΔR : (Δ : ℝ) ≤ 18 * lam * n := by rw [hlam]; linarith
  -- the bounded right inverse
  set mB : ℕ := ⌊δ * n⌋₊ with hmB
  have hmB1 : δ * n - 1 < mB := Nat.sub_one_lt_floor _
  have hmB2 : (mB : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hmBk : ∀ X, mB ≤ ksz lab X := by
    intro X; have : (mB : ℝ) ≤ ksz lab X := hmB2.trans (hcls X); exact_mod_cast this
  have h512 : 512 ≤ mB := by
    have : (512 : ℝ) ≤ mB := by
      have := pow_nonneg (show (0 : ℝ) ≤ R by linarith) 3; linarith
    exact_mod_cast this
  have hmR : 64 * R ^ 3 ≤ mB := by linarith
  have hbal : (Fintype.card (Fin n) : ℝ) ≤ R * mB := by
    rw [hcard, hR]; exact ar_bal hδ hmB1 (by linarith)
  have hΔseed : 8 * Kc * C₀ ^ 2 * Δ ≤ Fintype.card (Fin n) := by
    rw [hcard]; exact ar_seed hKc0 hn0.le hΔR L1
  obtain ⟨μ, hμ, -⟩ := residual_seed_k lab hk o hR1 hmBk h512 hmR hbal hδ hη hcls'
    (by rw [hcard]; linarith) ha P hPall hPd hdeg hΔseed
  set L := P.biUnion triEdges with hL
  -- H2, H3, H4 on `K_n − L`
  have hbig : BigRk lab L := bigRk_of_deg hdeg (fun X => by
    have : ((k + 4) * (Δ + 1) : ℝ) < ksz lab X :=
      ar_big (Nat.cast_nonneg k) hlam0.le hn0.le hΔR L6 hδnk (hcls X)
    exact_mod_cast this)
  obtain ⟨ob, hob, hobadj⟩ := exists_baseK hbig (⟨0, by
    have : (0 : ℝ) < n := hn0; exact_mod_cast this⟩ : Fin n)
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X h
    simp only [nx] at h
    split_ifs at h with h0
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn' : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]; obtain ⟨m', hm'⟩ := hodd; exact ⟨m', by omega⟩
  have H2 : IsPhysical (rHostK lab L) (bicF k) (edges (rHostK lab L)) :=
    residual_physicalK hbig hob hnx hobadj o P hPall hPd hL hn' heven
      (pair_of_div (ksz lab) hsum hdiv)
  obtain ⟨d10, d4⟩ := ar_D (Nat.cast_nonneg Δ) hn0.le hΔR L5 hδn20
  have hΔ4 : 4 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d4
  have hΔ10 : 10 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d10
  have H3 := commonNbr_mono (residual_H3K hdeg hcls' hΔ4) (ar_sq hδ hδ1)
  have H4 := residual_H4K hdeg hδ hcls' hΔ10
  obtain ⟨D, hD⟩ := hT (rHostK lab L) (by rw [Fintype.card_fin]; exact le_of_max_le_left hn)
    ⟨μ, hμ⟩ H2 H3 H4
  exact ⟨D ∪ P, union_decomp lab hPall hPd hD, subset_union_right⟩

end CDRBicolour.KBicolor
