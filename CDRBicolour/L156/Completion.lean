/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L156.Operator

/-!
# L156: states with fixed quotas

`RowStateQ`: as `RowState` of L181 with the quotas `μ₀` fixed and bounded by `ρ`.  The clean
colour of a move is now taken in a set `H` of colours of multiplicity exactly `ρ`
(`exists_cleanQ`), so that `μ₀ x ≥ μ₀ p` and the move keeps every quota (`RowStateQ.move`).
-/

@[expose] public section

namespace CDRBicolour.L156

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix CDRBicolour.L181

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {W : Finset Cl} {μ₀ : Cl → ℕ}

/-- The state of the row-by-row completion with fixed quotas. -/
structure RowStateQ (G : SimpleGraph Rw) [DecidableRel G.Adj] (W : Finset Cl) (μ₀ : Cl → ℕ)
    (ρ c₀ : ℕ) (s₀ : Rw → ℕ) (D : Finset Rw) (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) :
    Prop where
  good : GoodQ G W μ₀ χ M
  bound : ∀ v, v ∉ W → μ₀ v ≤ ρ
  done : ∀ j ∈ D, IsPerfectPairing (M j) (miss G χ j)
  openW : ∀ j, j ∉ D → W ⊆ cover (M j)
  openC : ∀ j, j ∉ D → (cover (M j)).card ≤ c₀
  openS : ∀ j, j ∉ D → (cover (M j)).card + 4 ≤ (miss G χ j).card
  size : ∀ j, (miss G χ j).card = s₀ j

variable {ρ c₀ : ℕ} {s₀ : Rw → ℕ} {D : Finset Rw}

theorem RowStateQ.support {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowStateQ G W μ₀ ρ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) {r : Cl}
    (hr : r ∈ miss G χ j₀ \ cover (M j₀)) :
    r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W := by
  rw [mem_sdiff] at hr
  exact ⟨hr.1, hr.2, fun h => hr.2 (hs.openW j₀ hj₀ h)⟩

theorem RowStateQ.move {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowStateQ G W μ₀ ρ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) {p x : Cl}
    (hp : p ∈ miss G χ j₀) (hpc : p ∉ cover (M j₀)) (hx : x ∉ miss G χ j₀) (hxρ : μ₀ x = ρ) :
    ∃ χ' M', RowStateQ G W μ₀ ρ c₀ s₀ D χ' M' ∧ MoveOK G j₀ p x χ M χ' M' := by
  have hpW : p ∉ W := fun h => hpc (hs.openW j₀ hj₀ h)
  obtain ⟨χ', M', hg, hperf, hW, hcov, hmiss, hfix, hmiss₀, hkeep, hroot⟩ :=
    port_moveQ hs.good hp hpc (hs.openW j₀ hj₀) hx (by rw [hxρ]; exact hs.bound p hpW)
  refine ⟨χ', M', ⟨hg, hs.bound, fun j hj => hperf j (hs.done j hj),
    fun j hj => hW j (hs.openW j hj), fun j hj => by rw [hcov]; exact hs.openC j hj,
    fun j hj => by rw [hcov, hmiss]; exact hs.openS j hj,
    fun j => (hmiss j).trans (hs.size j)⟩, ⟨hfix, hmiss₀, hkeep, hroot⟩⟩

/-- Pairs at a support point are owned by distinct other rows missing it. -/
theorem card_used_leQ {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hg : GoodQ G W μ₀ χ M)
    (hρ : ∀ v, v ∉ W → μ₀ v ≤ ρ)
    {j₀ : Rw} {r : Cl} (hr : r ∈ miss G χ j₀) (hrc : r ∉ cover (M j₀)) (hrW : r ∉ W) :
    (univ.filter fun v => ∃ j, s(r, v) ∈ M j).card ≤ ρ - 1 := by
  classical
  let f : Cl → Rw := fun v => if h : ∃ j, s(r, v) ∈ M j then Classical.choose h else j₀
  have hmaps : ∀ v ∈ univ.filter (fun v => ∃ j, s(r, v) ∈ M j),
      f v ∈ (univ.filter fun j => r ∈ miss G χ j).erase j₀ := by
    intro v hv
    have hv' := (mem_filter.1 hv).2
    have hspec := Classical.choose_spec hv'
    simp only [f, dif_pos hv', mem_erase, mem_filter, mem_univ, true_and]
    refine ⟨?_, miss_of_pair hg.proper hg.pairs hspec⟩
    intro h; rw [h] at hspec
    exact hrc (mem_cover.2 ⟨_, hspec, Sym2.mem_mk_left _ _⟩)
  have hinj : Set.InjOn f (univ.filter fun v => ∃ j, s(r, v) ∈ M j) := by
    intro v hv v' hv' h
    have hv1 := (mem_filter.1 (mem_coe.1 hv)).2
    have hv2 := (mem_filter.1 (mem_coe.1 hv')).2
    have h1 := Classical.choose_spec hv1
    have h2 := Classical.choose_spec hv2
    simp only [f, dif_pos hv1, dif_pos hv2] at h
    rw [h] at h1
    exact pair_unique hg.proper hg.pairs hg.disj h1 h2
  have h := card_le_card_of_injOn f (fun v hv => hmaps v hv) hinj
  have hm : (univ.filter fun j => r ∈ miss G χ j).card = mult G χ r := rfl
  rw [card_erase_of_mem (by simpa using hr), hm] at h
  have h1 := hg.fix r hrW
  have h2 := hρ r hrW
  omega

/-- A clean colour: outside `miss j₀` and in no old pair with a point of `I`. -/
theorem exists_cleanQ {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hg : GoodQ G W μ₀ χ M)
    (hρ : ∀ v, v ∉ W → μ₀ v ≤ ρ) (H : Finset Cl) (hH : ∀ v ∈ H, μ₀ v = ρ)
    {j₀ : Rw} (I : Finset Cl) (hI : ∀ r ∈ I, r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W)
    (hroom : (miss G χ j₀).card + I.card * (ρ - 1) < H.card) :
    ∃ x, μ₀ x = ρ ∧ x ∉ miss G χ j₀ ∧ ∀ r ∈ I, ∀ j, s(x, r) ∉ M j := by
  classical
  set B := miss G χ j₀ ∪ I.biUnion fun r => univ.filter fun v => ∃ j, s(r, v) ∈ M j
  have hB : B.card < H.card := by
    refine lt_of_le_of_lt ((card_union_le _ _).trans (Nat.add_le_add_left
      (card_biUnion_le.trans ?_) _)) hroom
    calc ∑ r ∈ I, (univ.filter fun v => ∃ j, s(r, v) ∈ M j).card ≤ ∑ _r ∈ I, (ρ - 1) :=
          sum_le_sum fun r hr => card_used_leQ hg hρ (hI r hr).1 (hI r hr).2.1 (hI r hr).2.2
      _ = I.card * (ρ - 1) := by rw [sum_const, smul_eq_mul]
  obtain ⟨x, hxH, hx⟩ := exists_mem_notMem_of_card_lt_card (s := B) (t := H) hB
  refine ⟨x, hH x hxH, fun h => hx (mem_union_left _ h), fun r hr j hj => hx (mem_union_right _
    (mem_biUnion.2 ⟨r, hr, ?_⟩))⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨j, by rw [Sym2.eq_swap]; exact hj⟩

end CDRBicolour.L156
