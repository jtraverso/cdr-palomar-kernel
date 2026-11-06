/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Basic
public import CDRBicolour.L184.NearPerfect
public import CDRBicolour.Combinatorics.Involution

/-!
# L184, part 2: late AAC labelling and the final assembly

Colour classes `A = col⁻¹ 0`, `B = col⁻¹ 1`, `C = col⁻¹ 2`.  A *prefix* `P` (the
AAB/ABB/BBC/BCC blocks of L182) covers every pair exactly once, except the **reserved** pairs:
all `AC` pairs, the pairs `{x, μ x}` of a reserved perfect matching `μ` of `A`, and the edges
of the residual graph `F` on `C`; it covers no reserved pair.

If `F` is properly edge-coloured with `|A|` colours, `|C|` is odd, `2|E(F)| = |A|(|C|-1)` and
`|A| - deg_F v` is even for every `v`, then (`l184_assembly`) the prefix extends to a Steiner
triple system all of whose blocks see exactly two colours:

* each colour class `i` is a near-perfect matching omitting one point `ω i` (part 1);
* classes are paired inside each fibre of `ω` by an involution `σ` (pairing lemma), and the
  pairs are matched with `μ` through a bijection `φ : colours ≃ A` with `φ ∘ σ = μ ∘ φ`
  (conjugacy lemma) — the AAC labels are assigned only now, as in L184;
* new blocks: `ACC = {φ(colour e)} ∪ e` for `e ∈ E(F)`, and `AAC = {φ i, φ (σ i), ω i}`.
-/

@[expose] public section

namespace CDRBicolour.L184

open Finset LeanPool.Vizing.ColourClasses

variable {V : Type*} [Fintype V] [DecidableEq V] (col : V → Fin 3)

/-- The classes `A` and `C` as types. -/
abbrev AType := {v : V // col v = 0}
abbrev CType := {v : V // col v = 2}

/-- Pairs that the prefix leaves for the AAC/ACC stage. -/
def Reserved (μ : AType col → AType col) (F : SimpleGraph (CType col)) (x y : V) : Prop :=
  (col x = 0 ∧ col y = 2) ∨ (col x = 2 ∧ col y = 0) ∨
    (∃ hx : col x = 0, y = (μ ⟨x, hx⟩).1) ∨
    (∃ hx : col x = 2, ∃ hy : col y = 2, F.Adj ⟨x, hx⟩ ⟨y, hy⟩)

section Blocks

variable {col} {k : ℕ} (ψ : Fin k → V) (σ : Fin k → Fin k) (ω : Fin k → CType col)
  (colour : Sym2 (CType col) → Fin k)

/-- The ACC block of an edge `e` of `F`. -/
def accBlock (e : Sym2 (CType col)) : Finset V :=
  insert (ψ (colour e)) (e.toFinset.map (Function.Embedding.subtype _))

/-- The AAC block of the colour pair `{i, σ i}`. -/
def aacBlock (i : Fin k) : Finset V := {ψ i, ψ (σ i), (ω i).1}

theorem mem_accBlock (e : Sym2 (CType col)) (v : V) :
    v ∈ accBlock ψ colour e ↔ v = ψ (colour e) ∨ ∃ c ∈ e, c.1 = v := by
  simp [accBlock, Sym2.mem_toFinset]

theorem mem_aacBlock (i : Fin k) (v : V) :
    v ∈ aacBlock ψ σ ω i ↔ v = ψ i ∨ v = ψ (σ i) ∨ v = (ω i).1 := by
  simp [aacBlock]

end Blocks

/-- **L184 (assembly).** -/
theorem l184_assembly
    (μ : AType col → AType col) (hμ : ∀ u, μ (μ u) = u) (hμ' : ∀ u, μ u ≠ u)
    (F : SimpleGraph (CType col)) [DecidableRel F.Adj]
    (colour : Sym2 (CType col) → Fin (Fintype.card (AType col)))
    (hproper : ProperOn F.edgeFinset colour)
    (hodd : Odd (Fintype.card (CType col)))
    (hE : 2 * F.edgeFinset.card = Fintype.card (AType col) * (Fintype.card (CType col) - 1))
    (heven : ∀ v, Even (Fintype.card (AType col) - F.degree v))
    (P : Finset (Finset V)) (hP3 : ∀ B ∈ P, B.card = 3)
    (hPbic : ∀ B ∈ P, (B.image col).card = 2)
    (hPres : ∀ x y, x ≠ y → Reserved col μ F x y → ∀ B ∈ P, ¬ (x ∈ B ∧ y ∈ B))
    (hPcov : ∀ x y, x ≠ y → ¬ Reserved col μ F x y → ∃! B, B ∈ P ∧ x ∈ B ∧ y ∈ B) :
    ∃ S : STS V, IsStrictBicolouring S col := by
  classical
  -- omitted points, pairing, labelling
  set ω := omitted hproper hodd hE with hωdef
  have hfib : ∀ v, Even (univ.filter fun i => ω i = v).card := by
    intro v; rw [hωdef, card_omitted_fibre hproper hodd hE v]; exact heven v
  obtain ⟨σ, hσ, hσ', hωσ⟩ := exists_pairing_of_even_fibres ω hfib
  obtain ⟨φ, hφbij, hφσ⟩ := exists_conj_of_card_eq σ μ hσ hσ' hμ hμ' (Fintype.card_fin _)
  set ψ : Fin (Fintype.card (AType col)) → V := fun i => (φ i).1 with hψdef
  have hψA : ∀ i, col (ψ i) = 0 := fun i => (φ i).2
  have hψinj : Function.Injective ψ := fun i j h => hφbij.1 (Subtype.ext h)
  have hψσ : ∀ i, ψ (σ i) = (μ (φ i)).1 := fun i => by simp [hψdef, hφσ]
  have hA_eq : ∀ x, col x = 0 → ∃ i, ψ i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := hφbij.2 ⟨x, hx⟩
    exact ⟨i, by simp [hψdef, hi]⟩
  have hcovered : ∀ (i : Fin (Fintype.card (AType col))) (c : CType col), c ≠ ω i →
      ∃ e ∈ F.edgeFinset, colour e = i ∧ c ∈ e := by
    intro i c hc
    have := (mem_coveredBy_iff_ne_omitted hproper hodd hE i c).2 hc
    simp only [coveredBy, mem_biUnion, mem_colourClass, Sym2.mem_toFinset] at this
    obtain ⟨e, ⟨he, hce⟩, hce'⟩ := this
    exact ⟨e, he, hce, hce'⟩
  have hnotcovered : ∀ (i : Fin (Fintype.card (AType col))) (e : Sym2 (CType col)), e ∈ F.edgeFinset → colour e = i →
      ω i ∉ e := by
    intro i e he hce hω
    have hmem : ω i ∈ coveredBy F colour i := by
      simp only [coveredBy, mem_biUnion, mem_colourClass, Sym2.mem_toFinset]
      exact ⟨e, ⟨he, hce⟩, hω⟩
    exact (mem_coveredBy_iff_ne_omitted hproper hodd hE i (ω i)).1 hmem rfl
  have hmatch : ∀ (e f : Sym2 (CType col)), e ∈ F.edgeFinset → f ∈ F.edgeFinset →
      colour e = colour f → ∀ c, c ∈ e → c ∈ f → e = f := by
    intro e f he hf hef c hce hcf
    by_contra hne
    exact Finset.disjoint_left.1 (hproper e he f hf hne hef) (Sym2.mem_toFinset.2 hce)
      (Sym2.mem_toFinset.2 hcf)
  -- the blocks
  set ACC := F.edgeFinset.image (accBlock ψ colour) with hACC
  set AAC := (univ : Finset (Fin (Fintype.card (AType col)))).image (aacBlock ψ σ ω) with hAAC
  set blocks := P ∪ ACC ∪ AAC with hblocks
  have hcolC : ∀ c : CType col, col c.1 = 2 := fun c => c.2
  -- cardinalities
  have hACC3 : ∀ e ∈ F.edgeFinset, (accBlock ψ colour e).card = 3 := by
    intro e he
    have hnot : ψ (colour e) ∉ e.toFinset.map (Function.Embedding.subtype _) := by
      simp only [mem_map, Sym2.mem_toFinset, Function.Embedding.subtype_apply, not_exists,
        not_and]
      intro c _ hc
      have := hψA (colour e); rw [← hc, hcolC c] at this; exact absurd this (by decide)
    rw [accBlock, card_insert_of_notMem hnot, card_map,
      Sym2.card_toFinset_of_not_isDiag e (SimpleGraph.not_isDiag_of_mem_edgeFinset he)]
  have hAAC3 : ∀ i, (aacBlock ψ σ ω i).card = 3 := by
    intro i
    have h1 : ψ i ≠ ψ (σ i) := fun h => hσ' i (hψinj h).symm
    have h2 : ψ i ≠ (ω i).1 := by
      intro h; have := hψA i; rw [h, hcolC] at this; exact absurd this (by decide)
    have h3 : ψ (σ i) ≠ (ω i).1 := by
      intro h; have := hψA (σ i); rw [h, hcolC] at this; exact absurd this (by decide)
    rw [aacBlock, card_insert_of_notMem (by simp [h1, h2]), card_insert_of_notMem (by simp [h3]),
      card_singleton]
  -- colour images
  have himage02 : ∀ B : Finset V, (∃ x ∈ B, col x = 0) → (∃ x ∈ B, col x = 2) →
      (∀ x ∈ B, col x = 0 ∨ col x = 2) → (B.image col).card = 2 := by
    intro B ⟨x, hx, hx0⟩ ⟨y, hy, hy2⟩ hall
    have : B.image col = {0, 2} := by
      ext t
      simp only [mem_image, mem_insert, mem_singleton]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hall z hz
      · rintro (rfl | rfl)
        · exact ⟨x, hx, hx0⟩
        · exact ⟨y, hy, hy2⟩
    rw [this]; decide
  have hACCbic : ∀ e ∈ F.edgeFinset, ((accBlock ψ colour e).image col).card = 2 := by
    intro e he
    obtain ⟨u, w⟩ := e
    refine himage02 _ ⟨ψ (colour s(u, w)), by simp [accBlock], hψA _⟩
      ⟨u.1, by rw [mem_accBlock]; exact Or.inr ⟨u, Sym2.mem_mk_left _ _, rfl⟩, hcolC u⟩ ?_
    intro x hx
    rw [mem_accBlock] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact Or.inl (hψA _)
    · exact Or.inr (hcolC c)
  have hAACbic : ∀ i, ((aacBlock ψ σ ω i).image col).card = 2 := by
    intro i
    refine himage02 _ ⟨ψ i, by simp [aacBlock], hψA i⟩ ⟨(ω i).1, by simp [aacBlock], hcolC _⟩ ?_
    intro x hx
    rw [mem_aacBlock] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (hψA _)
    · exact Or.inl (hψA _)
    · exact Or.inr (hcolC _)
  -- new blocks only contain reserved pairs
  have hACCres : ∀ e ∈ F.edgeFinset, ∀ x y, x ≠ y → x ∈ accBlock ψ colour e →
      y ∈ accBlock ψ colour e → Reserved col μ F x y := by
    intro e he x y hxy hx hy
    rw [mem_accBlock] at hx hy
    rcases hx with rfl | ⟨c, hc, rfl⟩ <;> rcases hy with rfl | ⟨d, hd, rfl⟩
    · exact absurd rfl hxy
    · exact Or.inl ⟨hψA _, hcolC d⟩
    · exact Or.inr (Or.inl ⟨hcolC c, hψA _⟩)
    · refine Or.inr (Or.inr (Or.inr ⟨c.2, d.2, ?_⟩))
      have hcd : c ≠ d := fun h => hxy (by rw [h])
      have hadj : F.Adj c d := by
        have hmem : e = s(c, d) := (Sym2.mem_and_mem_iff hcd).1 ⟨hc, hd⟩
        rw [hmem, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he
      exact hadj
  have hAACres : ∀ i, ∀ x y, x ≠ y → x ∈ aacBlock ψ σ ω i → y ∈ aacBlock ψ σ ω i →
      Reserved col μ F x y := by
    intro i x y hxy hx hy
    rw [mem_aacBlock] at hx hy
    have hμi : (μ (φ i)).1 = ψ (σ i) := (hψσ i).symm
    have hμσi : (μ (φ (σ i))).1 = ψ i := by
      rw [← hφσ, hσ]
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inr (Or.inr (Or.inl ⟨hψA i, by rw [← hμi]⟩))
    · exact Or.inl ⟨hψA i, hcolC _⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hψA (σ i), by rw [← hμσi]⟩))
    · exact absurd rfl hxy
    · exact Or.inl ⟨hψA _, hcolC _⟩
    · exact Or.inr (Or.inl ⟨hcolC _, hψA i⟩)
    · exact Or.inr (Or.inl ⟨hcolC _, hψA _⟩)
    · exact absurd rfl hxy
  -- uniqueness for reserved pairs among the new blocks
  -- membership helpers
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have hAccC : ∀ e v, col v = 2 → v ∈ accBlock ψ colour e → ∃ c ∈ e, c.1 = v := by
    intro e v hv hmem
    rw [mem_accBlock] at hmem
    rcases hmem with rfl | h
    · exact absurd (hψA _ ▸ hv) (by decide)
    · exact h
  have hAccA : ∀ e v, col v = 0 → v ∈ accBlock ψ colour e → v = ψ (colour e) := by
    intro e v hv hmem
    rw [mem_accBlock] at hmem
    rcases hmem with h | ⟨c, -, rfl⟩
    · exact h
    · exact absurd ((hcolC c).symm.trans hv) (by decide)
  have hAacC : ∀ j v, col v = 2 → v ∈ aacBlock ψ σ ω j → v = (ω j).1 := by
    intro j v hv hmem
    rw [mem_aacBlock] at hmem
    rcases hmem with rfl | rfl | h
    · exact absurd ((hψA _).symm.trans hv) (by decide)
    · exact absurd ((hψA _).symm.trans hv) (by decide)
    · exact h
  have hAacA : ∀ j v, col v = 0 → v ∈ aacBlock ψ σ ω j → v = ψ j ∨ v = ψ (σ j) := by
    intro j v hv hmem
    rw [mem_aacBlock] at hmem
    rcases hmem with h | h | rfl
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ((hcolC _).symm.trans hv) (by decide)
  have haacσ : ∀ j, aacBlock ψ σ ω (σ j) = aacBlock ψ σ ω j := by
    intro j
    ext v
    simp only [mem_aacBlock, hσ, hωσ]
    tauto
  have hmemBlocks : ∀ B, B ∈ blocks →
      B ∈ P ∨ (∃ e ∈ F.edgeFinset, B = accBlock ψ colour e) ∨ ∃ j, B = aacBlock ψ σ ω j := by
    intro B hB
    simp only [hblocks, mem_union, hACC, hAAC, mem_image, mem_univ, true_and] at hB
    rcases hB with (hB | ⟨e, he, rfl⟩) | ⟨j, rfl⟩
    · exact Or.inl hB
    · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, rfl⟩)
  have hAccMem : ∀ e ∈ F.edgeFinset, accBlock ψ colour e ∈ blocks := by
    intro e he; simp only [hblocks, mem_union, hACC, mem_image]; exact Or.inl (Or.inr ⟨e, he, rfl⟩)
  have hAacMem : ∀ j, aacBlock ψ σ ω j ∈ blocks := by
    intro j; simp only [hblocks, mem_union, hAAC, mem_image, mem_univ, true_and]
    exact Or.inr ⟨j, rfl⟩
  -- AC pairs
  have hAC : ∀ x y, col x = 0 → col y = 2 → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B := by
    intro x y hx hy
    have hxy : x ≠ y := fun h => h02 (hx.symm.trans (h ▸ hy))
    have hres : Reserved col μ F x y := Or.inl ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := hA_eq x hx
    set c : CType col := ⟨y, hy⟩
    by_cases hc : c = ω i
    · refine ⟨aacBlock ψ σ ω i, ⟨hAacMem i, by simp [aacBlock], ?_⟩, ?_⟩
      · rw [mem_aacBlock]; right; right; rw [← hc]
      · rintro B' ⟨hB', hx', hy'⟩
        rcases hmemBlocks B' hB' with hP | ⟨e, he, rfl⟩ | ⟨j, rfl⟩
        · exact absurd ⟨hx', hy'⟩ (hPres _ y hxy hres B' hP)
        · have h1 := hψinj (hAccA e _ (hψA i) hx')
          obtain ⟨d, hd, hdy⟩ := hAccC e y hy hy'
          have hdc : d = c := Subtype.ext hdy
          exact absurd (by rw [← hc, ← hdc]; exact hd) (hnotcovered i e he h1.symm)
        · rcases hAacA j _ (hψA i) hx' with h | h
          · rw [hψinj h]
          · rw [hψinj h, haacσ]
    · obtain ⟨e, he, hce, hcin⟩ := hcovered i c hc
      refine ⟨accBlock ψ colour e, ⟨hAccMem e he, ?_, ?_⟩, ?_⟩
      · rw [mem_accBlock, hce]; exact Or.inl rfl
      · rw [mem_accBlock]; exact Or.inr ⟨c, hcin, rfl⟩
      · rintro B' ⟨hB', hx', hy'⟩
        rcases hmemBlocks B' hB' with hP | ⟨f, hf, rfl⟩ | ⟨j, rfl⟩
        · exact absurd ⟨hx', hy'⟩ (hPres _ y hxy hres B' hP)
        · have h1 := hψinj (hAccA f _ (hψA i) hx')
          obtain ⟨d, hd, hdy⟩ := hAccC f y hy hy'
          have hdc : d = c := Subtype.ext hdy
          rw [hmatch f e hf he (by rw [← h1, hce]) c (hdc ▸ hd) hcin]
        · have hyω := hAacC j y hy hy'
          have hcj : c = ω j := Subtype.ext hyω
          rcases hAacA j _ (hψA i) hx' with h | h
          · exact absurd (hcj.trans (by rw [hψinj h])) hc
          · exact absurd (hcj.trans (by rw [← hωσ j, hψinj h])) hc
  have hnew_unique : ∀ x y, x ≠ y → Reserved col μ F x y →
      ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B := by
    intro x y hxy hres
    rcases hres with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hyμ⟩ | ⟨hx, hy, hadj⟩
    · exact hAC x y hx hy
    · obtain ⟨B, ⟨hB, hyB, hxB⟩, hu⟩ := hAC y x hy hx
      exact ⟨B, ⟨hB, hxB, hyB⟩, fun B' ⟨h1, h2, h3⟩ => hu B' ⟨h1, h3, h2⟩⟩
    · -- AA pair of the reserved matching
      obtain ⟨i, hi⟩ := hA_eq x hx
      have hφi : φ i = ⟨x, hx⟩ := Subtype.ext hi
      have hyψ : y = ψ (σ i) := by rw [hψσ, hφi]; exact hyμ
      refine ⟨aacBlock ψ σ ω i, ⟨hAacMem i, by rw [mem_aacBlock]; exact Or.inl hi.symm,
        by rw [mem_aacBlock]; exact Or.inr (Or.inl hyψ)⟩, ?_⟩
      rintro B' ⟨hB', hx', hy'⟩
      have hres : Reserved col μ F x y := Or.inr (Or.inr (Or.inl ⟨hx, hyμ⟩))
      have hy0 : col y = 0 := by rw [hyψ]; exact hψA _
      rcases hmemBlocks B' hB' with hP | ⟨e, he, rfl⟩ | ⟨j, rfl⟩
      · exact absurd ⟨hx', hy'⟩ (hPres _ _ hxy hres B' hP)
      · exact absurd ((hAccA e x hx hx').trans (hAccA e y hy0 hy').symm) hxy
      · rcases hAacA j x hx hx' with h1 | h1
        · rw [← hi] at h1; rw [hψinj h1]
        · rw [← hi] at h1; rw [hψinj h1, haacσ]
    · -- CC edge of F
      set c : CType col := ⟨x, hx⟩
      set d : CType col := ⟨y, hy⟩
      have hcd : c ≠ d := fun h => hxy (congrArg Subtype.val h)
      have he : s(c, d) ∈ F.edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
      have hres : Reserved col μ F x y := Or.inr (Or.inr (Or.inr ⟨hx, hy, hadj⟩))
      refine ⟨accBlock ψ colour s(c, d), ⟨hAccMem _ he, ?_, ?_⟩, ?_⟩
      · rw [mem_accBlock]; exact Or.inr ⟨c, Sym2.mem_mk_left _ _, rfl⟩
      · rw [mem_accBlock]; exact Or.inr ⟨d, Sym2.mem_mk_right _ _, rfl⟩
      · rintro B' ⟨hB', hx', hy'⟩
        rcases hmemBlocks B' hB' with hP | ⟨f, hf, rfl⟩ | ⟨j, rfl⟩
        · exact absurd ⟨hx', hy'⟩ (hPres _ _ hxy hres B' hP)
        · obtain ⟨c', hc', hc'x⟩ := hAccC f x hx hx'
          obtain ⟨d', hd', hd'y⟩ := hAccC f y hy hy'
          have h1 : c' = c := Subtype.ext hc'x
          have h2 : d' = d := Subtype.ext hd'y
          rw [h1] at hc'; rw [h2] at hd'
          rw [(Sym2.mem_and_mem_iff hcd).1 ⟨hc', hd'⟩]
        · exact absurd ((hAacC j x hx hx').trans (hAacC j y hy hy').symm) hxy
  -- assemble
  refine ⟨⟨blocks, ?_, ?_⟩, ?_⟩
  · intro B hB
    simp only [hblocks, mem_union, hACC, hAAC, mem_image, mem_univ, true_and] at hB
    rcases hB with (hB | ⟨e, he, rfl⟩) | ⟨i, rfl⟩
    · exact hP3 B hB
    · exact hACC3 e he
    · exact hAAC3 i
  · intro x y hxy
    by_cases hres : Reserved col μ F x y
    · exact hnew_unique x y hxy hres
    · obtain ⟨B, ⟨hBP, hxB, hyB⟩, huniq⟩ := hPcov x y hxy hres
      refine ⟨B, ⟨by simp [hblocks, hBP], hxB, hyB⟩, ?_⟩
      rintro B' ⟨hB', hx', hy'⟩
      simp only [hblocks, mem_union, hACC, hAAC, mem_image, mem_univ, true_and] at hB'
      rcases hB' with (hB' | ⟨e, he, rfl⟩) | ⟨i, rfl⟩
      · exact huniq B' ⟨hB', hx', hy'⟩
      · exact absurd (hACCres e he x y hxy hx' hy') hres
      · exact absurd (hAACres i x y hxy hx' hy') hres
  · intro B hB
    simp only [hblocks, mem_union, hACC, hAAC, mem_image, mem_univ, true_and] at hB
    rcases hB with (hB | ⟨e, he, rfl⟩) | ⟨i, rfl⟩
    · exact hPbic B hB
    · exact hACCbic e he
    · exact hAACbic i

end CDRBicolour.L184
