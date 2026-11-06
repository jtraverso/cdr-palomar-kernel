/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Operator

/-!
# L181: completion of the rows (COMPLETION PROOF)

The rows are completed one at a time.  For the current row `j₀` with residual support
`S = miss j₀ \ cover (M j₀)`, a *tentative* matching `T` (free pairs inside `S`) is enlarged by
one or two port moves (`step`): with `T = ∅` three exposed points are used; otherwise two exposed
points `p, u` and a pair `ab ∈ T` (`xu`, `xz`, or `ab ↦ xa, zb`).  Each move needs a clean colour,
which exists when `|miss j₀| + 4(m+1) < |C|` (`exists_clean`).

The core loop `complete_all` takes this *room* inequality as a hypothesis `hR`, required only at
a maximum non-perfect tentative matching.  The bounded variant of L181 gives it outright; the
paper's variant derives it from the maximum-matching count (`MaxMatching`).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

/-! ### Pairing lemmas -/

section Pairing

variable {T A : Finset (Sym2 Cl)} {S S' : Finset Cl}

theorem IsPartialPairing.mono (h : IsPartialPairing T S) (hS : S ⊆ S') : IsPartialPairing T S' :=
  ⟨h.1, fun e he v hv => hS (h.2.1 e he v hv), h.2.2⟩

theorem cover_subset_of_partial (h : IsPartialPairing T S) : cover T ⊆ S := fun v hv => by
  obtain ⟨e, he, hve⟩ := mem_cover.1 hv; exact h.2.1 e he v hve

theorem isPartialPairing_empty (S : Finset Cl) : IsPartialPairing (∅ : Finset (Sym2 Cl)) S :=
  ⟨by simp, by simp, by simp⟩

theorem mem_cover_insert {e : Sym2 Cl} {v : Cl} : v ∈ cover (insert e T) ↔ v ∈ e ∨ v ∈ cover T := by
  simp only [mem_cover, mem_insert]
  constructor
  · rintro ⟨f, rfl | hf, hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨f, hf, hv⟩
  · rintro (hv | ⟨f, hf, hv⟩)
    · exact ⟨e, Or.inl rfl, hv⟩
    · exact ⟨f, Or.inr hf, hv⟩

theorem isPartialPairing_insert (h : IsPartialPairing T S) {a b : Cl} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (ha' : a ∉ cover T) (hb' : b ∉ cover T) :
    IsPartialPairing (insert s(a, b) T) S := by
  have key : ∀ f ∈ T, ∀ v, v ∈ s(a, b) → v ∈ f → False := by
    intro f hf v hv hvf
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha' (mem_cover.2 ⟨f, hf, hvf⟩)
    · exact hb' (mem_cover.2 ⟨f, hf, hvf⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · rw [Sym2.mk_isDiag_iff]; exact hab
    · exact h.1 e he
  · intro e he v hv
    rcases mem_insert.1 he with rfl | he
    · rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact ha
      · exact hb
    · exact h.2.1 e he v hv
  · intro e he f hf v hve hvf
    rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
    · rfl
    · exact (key f hf v hve hvf).elim
    · exact (key e he v hvf hve).elim
    · exact h.2.2 e he f hf v hve hvf

theorem isPartialPairing_erase (h : IsPartialPairing T S) (e : Sym2 Cl) :
    IsPartialPairing (T.erase e) S :=
  ⟨fun f hf => h.1 f (mem_of_mem_erase hf), fun f hf => h.2.1 f (mem_of_mem_erase hf),
    fun f hf g hg => h.2.2 f (mem_of_mem_erase hf) g (mem_of_mem_erase hg)⟩

theorem not_mem_cover_erase (h : IsPartialPairing T S) {e : Sym2 Cl} (he : e ∈ T) {v : Cl}
    (hv : v ∈ e) : v ∉ cover (T.erase e) := by
  intro hc
  obtain ⟨f, hf, hvf⟩ := mem_cover.1 hc
  rw [mem_erase] at hf
  exact hf.1 (h.2.2 f hf.2 e he v hvf hv)

theorem card_cover_eq (h : IsPartialPairing T S) : (cover T).card = 2 * T.card := by
  rw [cover, card_biUnion]
  · rw [sum_congr rfl fun e he => Sym2.card_toFinset_of_not_isDiag e (h.1 e he), sum_const,
      smul_eq_mul, mul_comm]
  · intro e he f hf hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact hne (h.2.2 e he f hf v (Sym2.mem_toFinset.1 hve) (Sym2.mem_toFinset.1 hvf))

theorem isPerfectPairing_of_cover (h : IsPartialPairing T S) (hc : S ⊆ cover T) :
    IsPerfectPairing T S :=
  ⟨h.1, h.2.1, fun v hv => by
    obtain ⟨e, he, hve⟩ := mem_cover.1 (hc hv)
    exact ⟨e, ⟨he, hve⟩, fun f ⟨hf, hvf⟩ => h.2.2 f hf e he v hvf hve⟩⟩

theorem isPerfectPairing_union (hA : IsPartialPairing A S)
    (hT : IsPerfectPairing T (S \ cover A)) : IsPerfectPairing (A ∪ T) S := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_union.1 he with he | he
    · exact hA.1 e he
    · exact hT.1 e he
  · intro e he v hv
    rcases mem_union.1 he with he | he
    · exact hA.2.1 e he v hv
    · exact (mem_sdiff.1 (hT.2.1 e he v hv)).1
  · intro v hv
    by_cases hvc : v ∈ cover A
    · obtain ⟨e, he, hve⟩ := mem_cover.1 hvc
      refine ⟨e, ⟨mem_union_left _ he, hve⟩, ?_⟩
      rintro f ⟨hf, hvf⟩
      rcases mem_union.1 hf with hf | hf
      · exact hA.2.2 f hf e he v hvf hve
      · exact absurd hvc (mem_sdiff.1 (hT.2.1 f hf v hvf)).2
    · obtain ⟨e, ⟨he, hve⟩, hu⟩ := hT.2.2 v (mem_sdiff.2 ⟨hv, hvc⟩)
      refine ⟨e, ⟨mem_union_right _ he, hve⟩, ?_⟩
      rintro f ⟨hf, hvf⟩
      rcases mem_union.1 hf with hf | hf
      · exact absurd (mem_cover.2 ⟨f, hf, hvf⟩) hvc
      · exact hu f ⟨hf, hvf⟩

end Pairing

/-! ### States -/

section States

variable {G : SimpleGraph Rw} [DecidableRel G.Adj] {W : Finset Cl} {m : ℕ}

/-- The state of the row-by-row completion: rows in `D` are complete; every open row has `W`
covered, at most `c₀` covered points and at least four points of residual support. -/
structure RowState (G : SimpleGraph Rw) [DecidableRel G.Adj] (W : Finset Cl) (m h₀ c₀ : ℕ)
    (s₀ : Rw → ℕ) (D : Finset Rw) (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) : Prop where
  good : Good G W m χ M
  high : (univ.filter fun v => v ∉ W ∧ mult G χ v = m + 2).card = h₀
  done : ∀ j ∈ D, IsPerfectPairing (M j) (miss G χ j)
  openW : ∀ j, j ∉ D → W ⊆ cover (M j)
  openC : ∀ j, j ∉ D → (cover (M j)).card ≤ c₀
  openS : ∀ j, j ∉ D → (cover (M j)).card + 4 ≤ (miss G χ j).card
  size : ∀ j, (miss G χ j).card = s₀ j

/-- The effect of one move `p → x` at the row `j₀`. -/
structure MoveOK (G : SimpleGraph Rw) [DecidableRel G.Adj] (j₀ : Rw) (p x : Cl)
    (χ : Sym2 Rw → Cl) (M : Rw → Finset (Sym2 Cl)) (χ' : Sym2 Rw → Cl)
    (M' : Rw → Finset (Sym2 Cl)) : Prop where
  fixed : M' j₀ = M j₀
  miss₀ : miss G χ' j₀ = insert x ((miss G χ j₀).erase p)
  keep : ∀ e, p ∉ e → x ∉ e → ((∃ j, e ∈ M' j) ↔ ∃ j, e ∈ M j)
  root : ∀ I : Finset Cl, (∀ r ∈ I, ∀ j, s(x, r) ∉ M j) →
    (I.filter fun r => r ≠ p ∧ ∃ j, s(x, r) ∈ M' j).card ≤ 1

/-- A tentative matching of the row `j₀`: free pairs inside the residual support. -/
def Tent (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl)
    (M : Rw → Finset (Sym2 Cl)) (j₀ : Rw) (T : Finset (Sym2 Cl)) : Prop :=
  IsPartialPairing T (miss G χ j₀ \ cover (M j₀)) ∧ ∀ e ∈ T, ∀ j, e ∉ M j

variable {h₀ c₀ : ℕ} {s₀ : Rw → ℕ} {D : Finset Rw}

theorem RowState.move {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowState G W m h₀ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) {p x : Cl}
    (hp : p ∈ miss G χ j₀) (hpc : p ∉ cover (M j₀)) (hx : x ∉ miss G χ j₀) :
    ∃ χ' M', RowState G W m h₀ c₀ s₀ D χ' M' ∧ MoveOK G j₀ p x χ M χ' M' := by
  obtain ⟨χ', M', hg, hhigh, hperf, hW, hcov, hmiss, hfix, hmiss₀, hkeep, hroot⟩ :=
    port_move hs.good hp hpc (hs.openW j₀ hj₀) hx
  refine ⟨χ', M', ⟨hg, hhigh.trans hs.high, fun j hj => hperf j (hs.done j hj),
    fun j hj => hW j (hs.openW j hj), fun j hj => by rw [hcov]; exact hs.openC j hj,
    fun j hj => by rw [hcov, hmiss]; exact hs.openS j hj,
    fun j => (hmiss j).trans (hs.size j)⟩, ⟨hfix, hmiss₀, hkeep, hroot⟩⟩

theorem RowState.support {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)}
    (hs : RowState G W m h₀ c₀ s₀ D χ M) {j₀ : Rw} (hj₀ : j₀ ∉ D) {r : Cl}
    (hr : r ∈ miss G χ j₀ \ cover (M j₀)) :
    r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W := by
  rw [mem_sdiff] at hr
  exact ⟨hr.1, hr.2, fun h => hr.2 (hs.openW j₀ hj₀ h)⟩

/-- Pairs at a support point are owned by distinct other rows missing it. -/
theorem card_used_le {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hg : Good G W m χ M)
    {j₀ : Rw} {r : Cl} (hr : r ∈ miss G χ j₀) (hrc : r ∉ cover (M j₀)) (hrW : r ∉ W) :
    (univ.filter fun v => ∃ j, s(r, v) ∈ M j).card ≤ m + 1 := by
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
  rcases hg.two r hrW with h' | h' <;> omega

/-- A clean colour: outside `miss j₀` and in no old pair with a point of `I`. -/
theorem exists_clean {χ : Sym2 Rw → Cl} {M : Rw → Finset (Sym2 Cl)} (hg : Good G W m χ M)
    {j₀ : Rw} (I : Finset Cl) (hI : ∀ r ∈ I, r ∈ miss G χ j₀ ∧ r ∉ cover (M j₀) ∧ r ∉ W)
    (hroom : (miss G χ j₀).card + I.card * (m + 1) < Fintype.card Cl) :
    ∃ x, x ∉ miss G χ j₀ ∧ ∀ r ∈ I, ∀ j, s(x, r) ∉ M j := by
  classical
  set B := miss G χ j₀ ∪ I.biUnion fun r => univ.filter fun v => ∃ j, s(r, v) ∈ M j
  have hB : B.card < Fintype.card Cl := by
    refine lt_of_le_of_lt ((card_union_le _ _).trans (Nat.add_le_add_left
      (card_biUnion_le.trans ?_) _)) hroom
    calc ∑ r ∈ I, (univ.filter fun v => ∃ j, s(r, v) ∈ M j).card ≤ ∑ _r ∈ I, (m + 1) :=
          sum_le_sum fun r hr => card_used_le hg (hI r hr).1 (hI r hr).2.1 (hI r hr).2.2
      _ = I.card * (m + 1) := by rw [sum_const, smul_eq_mul]
  obtain ⟨x, -, hx⟩ := exists_mem_notMem_of_card_lt_card (s := B) (t := univ)
    (by rwa [card_univ])
  refine ⟨x, fun h => hx (mem_union_left _ h), fun r hr j hj => hx (mem_union_right _
    (mem_biUnion.2 ⟨r, hr, ?_⟩))⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨j, by rw [Sym2.eq_swap]; exact hj⟩

/-- The residual support after a move. -/
theorem support_move {χ χ' : Sym2 Rw → Cl} {M M' : Rw → Finset (Sym2 Cl)} {j₀ : Rw} {p x : Cl}
    (h : MoveOK G j₀ p x χ M χ' M') (hxc : x ∉ cover (M j₀)) :
    miss G χ' j₀ \ cover (M' j₀) = insert x ((miss G χ j₀ \ cover (M j₀)).erase p) := by
  rw [h.fixed, h.miss₀]
  ext v
  simp only [mem_sdiff, mem_insert, mem_erase]
  constructor
  · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2, h3⟩
  · rintro (rfl | ⟨h1, h2, h3⟩)
    · exact ⟨Or.inl rfl, hxc⟩
    · exact ⟨Or.inr ⟨h1, h2⟩, h3⟩

/-- A tentative matching avoiding `p`, `x` survives the move. -/
theorem tent_move {χ χ' : Sym2 Rw → Cl} {M M' : Rw → Finset (Sym2 Cl)} {j₀ : Rw} {p x : Cl}
    {T : Finset (Sym2 Cl)} (hT : Tent G χ M j₀ T) (hpT : p ∉ cover T) (hx : x ∉ miss G χ j₀)
    (hxc : x ∉ cover (M j₀)) (h : MoveOK G j₀ p x χ M χ' M') : Tent G χ' M' j₀ T := by
  have hTS := cover_subset_of_partial hT.1
  refine ⟨?_, ?_⟩
  · rw [support_move h hxc]
    refine ⟨hT.1.1, fun e he v hv => ?_, hT.1.2.2⟩
    refine mem_insert_of_mem (mem_erase.2 ⟨?_, hT.1.2.1 e he v hv⟩)
    rintro rfl; exact hpT (mem_cover.2 ⟨e, he, hv⟩)
  · intro e he j hej
    have hpe : p ∉ e := fun hp => hpT (mem_cover.2 ⟨e, he, hp⟩)
    have hxe : x ∉ e := fun hx' =>
      hx (mem_sdiff.1 (hTS (mem_cover.2 ⟨e, he, hx'⟩))).1
    obtain ⟨j', hj'⟩ := (h.keep e hpe hxe).1 ⟨j, hej⟩
    exact hT.2 e he j' hj'

theorem free_move {χ χ' : Sym2 Rw → Cl} {M M' : Rw → Finset (Sym2 Cl)} {j₀ : Rw} {p x : Cl}
    (h : MoveOK G j₀ p x χ M χ' M') {e : Sym2 Cl} (hpe : p ∉ e) (hxe : x ∉ e)
    (hfree : ∀ j, e ∉ M j) : ∀ j, e ∉ M' j := by
  intro j hj
  obtain ⟨j', hj'⟩ := (h.keep e hpe hxe).1 ⟨j, hj⟩
  exact hfree j' hj'

/-- Root loss: two points of `I` cannot both acquire a pair with `x`. -/
theorem one_free {M' : Rw → Finset (Sym2 Cl)} {I : Finset Cl} {x p u v : Cl} (hu : u ∈ I)
    (hv : v ∈ I) (huv : u ≠ v) (hup : u ≠ p) (hvp : v ≠ p)
    (h : (I.filter fun r => r ≠ p ∧ ∃ j, s(x, r) ∈ M' j).card ≤ 1) :
    (∀ j, s(x, u) ∉ M' j) ∨ (∀ j, s(x, v) ∉ M' j) := by
  by_contra hno
  push_neg at hno
  obtain ⟨⟨ju, hju⟩, ⟨jv, hjv⟩⟩ := hno
  have hsub : ({u, v} : Finset Cl) ⊆ I.filter fun r => r ≠ p ∧ ∃ j, s(x, r) ∈ M' j := by
    intro r hr
    rw [mem_insert, mem_singleton] at hr
    rw [mem_filter]
    rcases hr with rfl | rfl
    · exact ⟨hu, hup, ju, hju⟩
    · exact ⟨hv, hvp, jv, hjv⟩
  have := card_le_card hsub
  rw [card_pair huv] at this
  omega

end States

end CDRBicolour.L181
