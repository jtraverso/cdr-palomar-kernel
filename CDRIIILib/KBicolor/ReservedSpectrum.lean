/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.ReservedCopies

/-!
# Exact correction without changing a prescribed residual decomposition

The available capacity is the number of retained copies on each cycle
coordinate, not `m²`. The final decomposition contains the whole residual
decomposition. In particular, any prescribed packing already in that
residual is left untouched by every switch.
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
  CDRBicolour.Absorption.Refined

variable {k n m : ℕ}

/-- Attach the prescribed blocks before switching the disjoint trade reserve. -/
theorem attach_prescribed (lab : Fin n → Fin k) (L : Finset (Sym2 (Fin n)))
    (Q : Finset (Finset (Fin n)))
    (hQall : ∀ T ∈ Q, IsAllowed (kHost lab) (bicF k) T)
    (hQdisj : (Q : Set (Finset (Fin n))).PairwiseDisjoint triEdges)
    (hLQ : Disjoint L (Q.biUnion triEdges)) (D : Finset (Finset (Fin n)))
    (hD : IsDecomposition (rHostK lab (L ∪ Q.biUnion triEdges)) (bicF k)
      (edges (rHostK lab (L ∪ Q.biUnion triEdges))) D) :
    IsDecomposition (rHostK lab L) (bicF k) (edges (rHostK lab L)) (D ∪ Q) := by
  classical
  have hQsub : ∀ T ∈ Q, triEdges T ⊆ Q.biUnion triEdges :=
    fun T hT e he => mem_biUnion.mpr ⟨T, hT, he⟩
  have hQa : ∀ T ∈ Q, IsAllowed (rHostK lab L) (bicF k) T := by
    intro T hT
    exact (gallowed_iff (lab := lab) (F := bicF k) L).mpr
      ⟨gmem_tri.mpr (hQall T hT), hLQ.symm.mono_left (hQsub T hT)⟩
  have hDa : ∀ T ∈ D, IsAllowed (rHostK lab L) (bicF k) T := by
    intro T hT
    have h := (gallowed_iff (lab := lab) (F := bicF k) (L ∪ Q.biUnion triEdges)).mp (hD.1 T hT)
    exact (gallowed_iff (lab := lab) (F := bicF k) L).mpr
      ⟨h.1, h.2.mono_right subset_union_left⟩
  have hDQ : ∀ T ∈ D, Disjoint (triEdges T) (Q.biUnion triEdges) := by
    intro T hT
    exact (disj_of_rHostK lab (hD.1 T hT)).mono_right subset_union_right
  refine ⟨fun T hT => (mem_union.mp hT).elim (hDa T) (hQa T), ?_, ?_⟩
  · intro T hT U hU hne
    rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
    · exact hD.2.1 hT hU hne
    · exact (hDQ T hT).mono_right (hQsub U hU)
    · exact ((hDQ U hU).mono_right (hQsub T hT)).symm
    · exact hQdisj hT hU hne
  · ext e
    have hc := Finset.ext_iff.mp hD.2.2 e
    simp only [mem_biUnion, mem_union] at hc ⊢
    constructor
    · rintro ⟨T, hT | hT, he⟩
      · have heD := hc.mp ⟨T, hT, he⟩
        induction e using Sym2.ind with
        | _ u v =>
          simp only [edges, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet,
            rG_adj] at heD ⊢
          exact ⟨fun h => heD.1 (mem_union_left _ h), heD.2⟩
      · induction e using Sym2.ind with
        | _ u v =>
          simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he
          have ha := (hQa T hT).2.1 u he.1.1 v he.1.2 he.2
          simpa only [edges, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet] using ha
    · intro he
      by_cases heQ : e ∈ Q.biUnion triEdges
      · obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
        exact ⟨T, Or.inr hT, heT⟩
      · have heD : e ∈ edges (rHostK lab (L ∪ Q.biUnion triEdges)) := by
          induction e using Sym2.ind with
          | _ u v =>
            simp only [edges, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet,
              rG_adj] at he ⊢
            exact ⟨fun h => (mem_union.mp h).elim he.1 heQ, he.2⟩
        obtain ⟨T, hT, heT⟩ := hc.mpr heD
        exact ⟨T, Or.inl hT, heT⟩

/-- Baseline contribution of the retained copies on a cycle coordinate. -/
def selectedBase (lab : Fin n → Fin k) (o : Fin k) [NeZero m]
    (P : Place lab (Coord o) m) (S : Finset (Coord o × ZMod m × ZMod m))
    (i : Coord o) : ℕ := ∑ c ∈ S, mcnt (P.τ c.1) T0m i.1.1 i.1.2

theorem selectedBase_le_Bn (lab : Fin n → Fin k) (o : Fin k) [NeZero m]
    (P : Place lab (Coord o) m) (S : Finset (Coord o × ZMod m × ZMod m)) (i : Coord o) :
    selectedBase lab o P S i ≤ Bn lab o P i := by
  unfold selectedBase Bn
  exact sum_le_sum_of_subset (subset_univ S)

/-- A finite number of switches can be chosen independently on every coordinate. -/
theorem exists_selected_switches {o : Fin k} [NeZero m]
    (S : Finset (Coord o × ZMod m × ZMod m)) (N : Coord o → ℕ)
    (hN : ∀ i, N i ≤ #(S.filter fun c => c.1 = i)) :
    ∃ σ : Coord o × ZMod m × ZMod m → Bool, ∀ i : Coord o,
      ∑ c ∈ S, (if σ c then (if c.1 = i then (-1 : ℤ) else 0) else 0) = -(N i : ℤ) := by
  classical
  have hex : ∀ i : Coord o, ∃ U : Finset (Coord o × ZMod m × ZMod m),
      U ⊆ S.filter (fun c => c.1 = i) ∧ #U = N i := fun i => exists_subset_card_eq (hN i)
  choose U hU hcard using hex
  refine ⟨fun c => decide (c ∈ U c.1), fun i => ?_⟩
  have he (c : Coord o × ZMod m × ZMod m) :
      (if decide (c ∈ U c.1) then (if c.1 = i then (-1 : ℤ) else 0) else 0) =
        if c ∈ U i then -1 else 0 := by
    by_cases hc : c.1 = i
    · simp [hc]
    · have hu : c ∉ U i := fun hu => hc (mem_filter.mp (hU i hu)).2
      simp [hc, hu]
  rw [sum_congr rfl (fun c _ => he c), ← sum_filter]
  have hf : S.filter (fun c => c ∈ U i) = U i := by
    ext c
    exact mem_filter.trans (and_iff_right_of_imp fun h => (mem_filter.mp (hU i h)).1)
  rw [hf, sum_const, hcard, nsmul_eq_mul]
  ring

/-- A sparse prescription leaves more correction capacity than the monitor error. -/
theorem retained_capacity_margin {lam n m delta g : ℝ}
    (hl : 0 ≤ lam) (hn : 0 ≤ n) (hm : lam * n / 4 ≤ m)
    (hd : delta ≤ lam ^ 2 / 256 * n) (hg : m ^ 2 ≤ g + n * delta) :
    m ^ 2 / 2 ≤ g ∧ lam ^ 2 / 512 * n ^ 2 ≤ g / 4 := by
  have hsq : (lam * n / 4) ^ 2 ≤ m ^ 2 :=
    pow_le_pow_left₀ (by positivity) hm 2
  have hdel := mul_le_mul_of_nonneg_left hd hn
  constructor <;> nlinarith

/-- Prescribed blocks and discarded copies stay within the old shift budget. -/
theorem prescribed_shift_budget {lam n m delta g b p : ℝ}
    (_hl : 0 ≤ lam) (hn : 0 ≤ n) (hm0 : 0 ≤ m) (hm : m ≤ lam * n)
    (hd : delta ≤ lam ^ 2 / 256 * n) (hg0 : 0 ≤ g) (hg : g ≤ m ^ 2)
    (hb0 : 0 ≤ b) (hb : b ≤ 9 * m ^ 2) (hp0 : 0 ≤ p) (hp : p ≤ n * delta) :
    |g / 2 - b - p| ≤ 38 * lam ^ 2 * n ^ 2 := by
  have hsq := pow_le_pow_left₀ hm0 hm 2
  have hdel := mul_le_mul_of_nonneg_left hd hn
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (lam * n)]

/-- Exact counts using only retained copies; every residual block is preserved. -/
theorem exact_from_selected (lab : Fin n → Fin k) (o : Fin k)
    [Fact m.Prime] (hm8 : 8 < m) (P : Place lab (Coord o) m) (hPτ : P.τ = tau3 o)
    (S : Finset (Coord o × ZMod m × ZMod m)) (E : Finset (Finset (Fin n)))
    (hE : IsDecomposition (rHostK lab (leaveSelected P S)) (bicF k)
      (edges (rHostK lab (leaveSelected P S))) E)
    (t : Fin k → Fin k → ℕ)
    (hpair : ∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y)
    (hrow : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1))
    (hclose : ∀ i : Coord o,
      |(kTypeCount lab E i.1.1 i.1.2 : ℝ) -
        ((t i.1.1 i.1.2 : ℝ) - selectedBase lab o P S i +
          (#(S.filter fun c => c.1 = i) : ℝ) / 2)| ≤
        (#(S.filter fun c => c.1 = i) : ℝ) / 4) :
    ∃ D, IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
      E ⊆ D ∧ ∀ X Y, X ≠ Y → kTypeCount lab D X Y = t X Y := by
  classical
  let z : Coord o → ℤ := fun i =>
    (kTypeCount lab E i.1.1 i.1.2 : ℤ) + selectedBase lab o P S i - t i.1.1 i.1.2
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ #(S.filter fun c => c.1 = i) := by
    intro i
    have hc := abs_le.mp (hclose i)
    have he : (z i : ℝ) = (kTypeCount lab E i.1.1 i.1.2 : ℝ) +
        selectedBase lab o P S i - t i.1.1 i.1.2 := by simp only [z]; push_cast; rfl
    have h0 : (0 : ℝ) ≤ #(S.filter fun c => c.1 = i) := Nat.cast_nonneg _
    constructor
    · have : (0 : ℝ) ≤ z i := by rw [he]; linarith
      exact_mod_cast this
    · have : (z i : ℝ) ≤ #(S.filter fun c => c.1 = i) := by rw [he]; linarith
      exact_mod_cast this
  obtain ⟨σ, hσ⟩ := exists_selected_switches S (fun i => (z i).toNat) (fun i => by
    have := (hz i).2; omega)
  let Q := packSelected P S σ
  have hQall := packSelected_allowed P S σ
  have hQdisj := packSelected_disj P hm8 S σ
  have hQleave := packSelected_leave P S σ
  have hE' : IsDecomposition (rHostK lab (Q.biUnion triEdges)) (bicF k)
      (edges (rHostK lab (Q.biUnion triEdges))) E := by rw [hQleave]; exact hE
  have hdec := union_decomp lab hQall hQdisj hE'
  have hEQ : Disjoint E Q := by
    rw [Finset.disjoint_left]
    intro T hTE hTQ
    obtain ⟨x, y, z', hxy, _, _, heT⟩ := card_eq_three.mp (hQall T hTQ).1
    have hedge : s(x, y) ∈ triEdges T := by rw [heT]; simp [triEdges, hxy]
    have hsub : s(x, y) ∈ leaveSelected P S := by
      rw [← hQleave]; exact mem_biUnion.mpr ⟨T, hTQ, hedge⟩
    exact disjoint_left.mp (disj_of_rHostK lab (hE.1 T hTE)) hedge hsub
  have hcount : ∀ X Y, kTypeCount lab (E ∪ Q) X Y =
      kTypeCount lab E X Y + kTypeCount lab Q X Y := by
    intro X Y
    unfold kTypeCount
    rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hEQ)]
  have hcoord : ∀ i : Coord o, kTypeCount lab (E ∪ Q) i.1.1 i.1.2 = t i.1.1 i.1.2 := by
    intro i
    have hPc := packSelected_count P hm8 S σ i.1.1 i.1.2
    have hsw : ∑ c ∈ S, (if σ c then
        ((mcnt (P.τ c.1) T1m i.1.1 i.1.2 : ℤ) - mcnt (P.τ c.1) T0m i.1.1 i.1.2) else 0) =
          -((z i).toNat : ℤ) := by
      rw [hPτ]
      simpa only [diff_coord] using hσ i
    rw [hsw] at hPc
    have hB : (selectedBase lab o P S i : ℤ) =
        ∑ c ∈ S, (mcnt (P.τ c.1) T0m i.1.1 i.1.2 : ℤ) := by
      unfold selectedBase; push_cast; rfl
    have hzi : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hz i).1
    have : (kTypeCount lab (E ∪ Q) i.1.1 i.1.2 : ℤ) = t i.1.1 i.1.2 := by
      rw [hcount]; push_cast; rw [hPc, ← hB, hzi]; simp only [z]; ring
    exact_mod_cast this
  refine ⟨E ∪ Q, hdec, subset_union_left, coord_determines o
    (fun X Y => kTypeCount lab (E ∪ Q) X Y) t (fun X Y h => ?_) (fun X => ?_) hcoord⟩
  · have h1 : 2 * (kTypeCount lab (E ∪ Q) X Y + kTypeCount lab (E ∪ Q) Y X) =
        ksz lab X * ksz lab Y := typeCount_pair lab hdec h
    have h2 := hpair X Y h
    show kTypeCount lab (E ∪ Q) X Y + kTypeCount lab (E ∪ Q) Y X = t X Y + t Y X
    omega
  · have h1 : 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), kTypeCount lab (E ∪ Q) X Y =
        ksz lab X * (ksz lab X - 1) := typeCount_row lab hdec X
    have h2 := hrow X
    show ∑ Y ∈ univ.filter (fun Y => Y ≠ X), kTypeCount lab (E ∪ Q) X Y =
      ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y
    omega

end CDRBicolour.KBicolor
