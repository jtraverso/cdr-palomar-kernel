/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V27.CoreInstance

@[expose] public section

/-!
# V27 — one root, several active components, inside the core

`coreAvail_biUnion` is `SelSimul.localAvail_biUnion` (same sequential placement over the
components, same windows `ζc ≥ ζ + (A+1)·|⋃ U k|`, `ρc ≥ ρ + 60`) for the core contract
`CoreAvail`: if every component's selector has its non-port vertices in `Wc`, so has the
assembled one.  Inside one root, a component's auxiliaries avoid all ports of the OTHER
components (they are in its deleted window) and its own ports (`portFree`).
-/

namespace S07V27

open Finset SelBridge SelTyped SelSimul

variable {V I : Type*} [DecidableEq V]

/-- A matching mode only uses covered vertices. -/
lemma mode_vert' {P : Finset (Sym2 V)} {W S : Finset V} {M : Finset (Sym2 V)}
    (hM : IsMode P W S M) {f : Sym2 V} (hf : f ∈ M) {y : V} (hy : y ∈ f) : y ∈ W ∪ S := by
  by_contra h; exact hM.2.2 y h f hf hy

/-- **Assembly of the single-root contract over disjoint port parts.** -/
theorem coreAvail_biUnion {κ : Type*} [DecidableEq κ] (G : SimpleGraph V) (lab : V → I)
    (F : Set (Multiset I)) (v : V) (C : Finset κ) (U : κ → Finset V)
    (Adm : κ → Finset V → Prop) {A ζ ρ ζc ρc : ℕ}
    (hdisj : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → Disjoint (U k) (U k'))
    (Wc : Finset V) (hav : ∀ k ∈ C, CoreAvail G lab F v (U k) (Adm k) A ζc ρc Wc)
    (hζ : ζ + (A + 1) * (C.biUnion U).card ≤ ζc) (hρ : ρ + 60 ≤ ρc) :
    CoreAvail G lab F v (C.biUnion U) (fun S => ∀ k ∈ C, Adm k (S ∩ U k)) A ζ ρ Wc := by
  intro Z0 Bf hZ0 hBf
  set CU := C.biUnion U with hCU
  have hUsub : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → U k' ⊆ CU \ U k := fun k hk k' hk' hne x hx =>
    mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨k', hk', hx⟩,
      fun h => Finset.disjoint_left.mp (hdisj k hk k' hk' hne) h hx⟩
  -- sequential placement over the parts
  have key : ∀ C' : Finset κ, C' ⊆ C → ∃ τ : κ → LocalSel V,
      (∀ k ∈ C', (τ k).Valid G lab F v (U k) (Adm k) (Z0 ∪ (CU \ U k)) Bf A) ∧
      (∀ k ∈ C', ∀ k' ∈ C', k ≠ k' → Disjoint (τ k).W (τ k').W) ∧
      (∀ k ∈ C', (τ k).W ⊆ Wc) := by
    intro C'
    induction C' using Finset.induction_on with
    | empty => intro _; exact ⟨fun _ => ⟨∅, ∅, fun _ => ∅⟩, by simp, by simp, by simp⟩
    | insert c C' hc ih =>
      intro hsub
      have hcC : c ∈ C := hsub (mem_insert_self c C')
      have hC'C : C' ⊆ C := (subset_insert c C').trans hsub
      obtain ⟨τ, hval, hW, hWc⟩ := ih hC'C
      -- vertex sets of the placed parts are pairwise disjoint
      have hvd : ∀ k ∈ C', ∀ k' ∈ C', k ≠ k' →
          Disjoint (U k ∪ (τ k).W) (U k' ∪ (τ k').W) := by
        intro k hk k' hk' hne
        rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
        refine ⟨⟨hdisj k (hC'C hk) k' (hC'C hk') hne, ?_⟩, ?_, hW k hk k' hk' hne⟩
        · exact ((hval k' hk').avoidZ.mono_right
            ((hUsub k' (hC'C hk') k (hC'C hk) (Ne.symm hne)).trans subset_union_right)).symm
        · exact (hval k hk).avoidZ.mono_right
            ((hUsub k (hC'C hk) k' (hC'C hk') hne).trans subset_union_right)
      set Z0' := Z0 ∪ (CU \ U c) ∪ C'.biUnion (fun k => (τ k).W) with hZ0'
      set Bf' := Bf ∪ C'.biUnion (fun k => (τ k).P) with hBf'
      have hcardU : ∑ k ∈ C', (U k).card ≤ CU.card := by
        rw [← card_biUnion (fun k hk k' hk' hne => hdisj k (hC'C hk) k' (hC'C hk') hne)]
        exact card_le_card (biUnion_subset_biUnion_of_subset_left _ hC'C)
      have hZc : Z0'.card ≤ ζc := by
        rw [hZ0']
        have h1 := card_union_le (Z0 ∪ (CU \ U c)) (C'.biUnion (fun k => (τ k).W))
        have h2 := card_union_le Z0 (CU \ U c)
        have h3 : (CU \ U c).card ≤ CU.card := card_le_card sdiff_subset
        have h4 : (C'.biUnion (fun k => (τ k).W)).card ≤ A * CU.card := by
          refine card_biUnion_le.trans ?_
          calc ∑ k ∈ C', ((τ k).W).card ≤ ∑ k ∈ C', A * (U k).card :=
                sum_le_sum fun k hk => (hval k hk).card_le
            _ = A * ∑ k ∈ C', (U k).card := by rw [mul_sum]
            _ ≤ A * CU.card := Nat.mul_le_mul_left _ hcardU
        have h5 : (A + 1) * CU.card = A * CU.card + CU.card := by ring
        omega
      have hBc : ∀ y, edeg Bf' y ≤ ρc := by
        intro y
        rw [hBf']
        have h1 := edeg_union_le Bf (C'.biUnion (fun k => (τ k).P)) y
        have h2 := edeg_biUnion_le C' (fun k => (τ k).P) (fun k => U k ∪ (τ k).W)
          (fun k hk => (hval k hk).deg_le)
          (fun k hk f hf y hy => mem_union.mpr ((hval k hk).supp f hf y hy)) y
        have h3 : (C'.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 1 := by
          rw [card_le_one]
          intro k hk k' hk'
          by_contra hne
          rw [mem_filter] at hk hk'
          exact Finset.disjoint_left.mp (hvd k hk.1 k' hk'.1 hne) hk.2 hk'.2
        have := hBf y
        have : 60 * (C'.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 60 := by omega
        omega
      obtain ⟨σc, hσc, hσcW⟩ := hav c hcC Z0' Bf' hZc hBc
      have hupd : ∀ k ∈ C', Function.update τ c σc k = τ k := fun k hk =>
        Function.update_of_ne (by rintro rfl; exact hc hk) _ _
      refine ⟨Function.update τ c σc, ?_, ?_, ?_⟩
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · rw [Function.update_self]
          exact hσc.mono (fun x hx => by rw [hZ0']; exact mem_union_left _ hx)
            (fun f hf => by rw [hBf']; exact mem_union_left _ hf)
        · rw [hupd k hk]; exact hval k hk
      · have hWc : ∀ k ∈ C', Disjoint σc.W (τ k).W := fun k hk =>
          hσc.avoidZ.mono_right (fun x hx => by
            rw [hZ0']; exact mem_union_right _ (mem_biUnion.mpr ⟨k, hk, hx⟩))
        intro k hk k' hk' hne
        rcases mem_insert.mp hk with hkc | hk <;> rcases mem_insert.mp hk' with hkc' | hk'
        · exact absurd (hkc.trans hkc'.symm) hne
        · rw [hkc, Function.update_self, hupd k' hk']; exact hWc k' hk'
        · rw [hkc', Function.update_self, hupd k hk]; exact (hWc k hk).symm
        · rw [hupd k hk, hupd k' hk']; exact hW k hk k' hk' hne
      · intro k hk
        rcases mem_insert.mp hk with rfl | hk
        · rw [Function.update_self]; exact hσcW
        · rw [hupd k hk]; exact hWc k hk
  obtain ⟨τ, hval, hW, hWc⟩ := key C (subset_refl _)
  -- the cells `U k ∪ W k` are pairwise disjoint
  have hvd : ∀ k ∈ C, ∀ k' ∈ C, k ≠ k' → Disjoint (U k ∪ (τ k).W) (U k' ∪ (τ k').W) := by
    intro k hk k' hk' hne
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hdisj k hk k' hk' hne, ?_⟩, ?_, hW k hk k' hk' hne⟩
    · exact ((hval k' hk').avoidZ.mono_right
        ((hUsub k' hk' k hk (Ne.symm hne)).trans subset_union_right)).symm
    · exact (hval k hk).avoidZ.mono_right ((hUsub k hk k' hk' hne).trans subset_union_right)
  have hone : ∀ y, (C.filter (fun k => y ∈ U k ∪ (τ k).W)).card ≤ 1 := by
    intro y
    rw [card_le_one]
    intro k hk k' hk'
    by_contra hne
    rw [mem_filter] at hk hk'
    exact Finset.disjoint_left.mp (hvd k hk.1 k' hk'.1 hne) hk.2 hk'.2
  have hcell : ∀ k ∈ C, ∀ k' ∈ C, ∀ y, y ∈ U k ∪ (τ k).W → y ∈ U k' ∪ (τ k').W → k = k' := by
    intro k hk k' hk' y h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (hvd k hk k' hk' hne) h1 h2
  refine ⟨⟨C.biUnion (fun k => (τ k).W), C.biUnion (fun k => (τ k).P),
    fun S => C.biUnion (fun k => (τ k).mode (S ∩ U k))⟩, ?_, ?_⟩
  refine
    { typed := ?_
      avoidB := ?_
      supp := ?_
      wing := ?_
      avoidZ := ?_
      portFree := ?_
      card_le := ?_
      deg_le := ?_
      modes := ?_ }
  · intro f hf
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    exact (hval k hk).typed f hf
  · rw [Finset.disjoint_left]
    intro f hf hfB
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hval k hk).avoidB hf hfB
  · intro f hf y hy
    obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
    rcases (hval k hk).supp f hf y hy with h | h
    · exact Or.inl (mem_biUnion.mpr ⟨k, hk, h⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨k, hk, h⟩)
  · intro w hw
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact (hval k hk).wing w hw
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact Finset.disjoint_left.mp (hval k hk).avoidZ hw (mem_union_left _ hwZ)
  · rw [Finset.disjoint_left]
    intro w hw hwU
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    obtain ⟨k', hk', hwU⟩ := mem_biUnion.mp hwU
    exact absurd (hcell k hk k' hk' w (mem_union_right _ hw) (mem_union_left _ hwU) ▸ hwU)
      (Finset.disjoint_left.mp (hval k hk).portFree hw)
  · refine card_biUnion_le.trans ?_
    calc ∑ k ∈ C, ((τ k).W).card ≤ ∑ k ∈ C, A * (U k).card :=
          sum_le_sum fun k hk => (hval k hk).card_le
      _ = A * ∑ k ∈ C, (U k).card := by rw [mul_sum]
      _ = A * CU.card := by rw [hCU, card_biUnion hdisj]
  · intro y
    refine (edeg_biUnion_le C (fun k => (τ k).P) (fun k => U k ∪ (τ k).W)
      (fun k hk => (hval k hk).deg_le)
      (fun k hk f hf y hy => mem_union.mpr ((hval k hk).supp f hf y hy)) y).trans ?_
    have := hone y
    omega
  · intro S hS hadm
    have hM : ∀ k ∈ C, IsMode (τ k).P (τ k).W (S ∩ U k) ((τ k).mode (S ∩ U k)) :=
      fun k hk => (hval k hk).modes _ inter_subset_right (hadm k hk)
    -- every covered vertex of the mode of `k` lies in the cell of `k`
    have hvert : ∀ k ∈ C, ∀ f ∈ (τ k).mode (S ∩ U k), ∀ y ∈ f, y ∈ U k ∪ (τ k).W := by
      intro k hk f hf y hy
      rcases mem_union.mp (mode_vert' (hM k hk) hf hy) with h | h
      · exact mem_union_right _ h
      · exact mem_union_left _ (mem_inter.mp h).2
    refine ⟨?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
      exact mem_biUnion.mpr ⟨k, hk, (hM k hk).1 hf⟩
    · intro x hx
      -- the cell of `x`
      obtain ⟨k, hk, hxk⟩ : ∃ k ∈ C, x ∈ (τ k).W ∪ (S ∩ U k) := by
        rcases mem_union.mp hx with hx | hx
        · obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
          exact ⟨k, hk, mem_union_left _ hx⟩
        · obtain ⟨k, hk, hxU⟩ := mem_biUnion.mp (hS hx)
          exact ⟨k, hk, mem_union_right _ (mem_inter.mpr ⟨hx, hxU⟩)⟩
      have hxcell : x ∈ U k ∪ (τ k).W := by
        rcases mem_union.mp hxk with h | h
        · exact mem_union_right _ h
        · exact mem_union_left _ (mem_inter.mp h).2
      have heq : (C.biUnion (fun k => (τ k).mode (S ∩ U k))).filter (fun e => x ∈ e) =
          ((τ k).mode (S ∩ U k)).filter (fun e => x ∈ e) := by
        ext f
        simp only [mem_filter, mem_biUnion]
        constructor
        · rintro ⟨⟨k', hk', hf⟩, hxf⟩
          have := hcell k hk k' hk' x hxcell (hvert k' hk' f hf x hxf)
          subst this
          exact ⟨hf, hxf⟩
        · rintro ⟨hf, hxf⟩
          exact ⟨⟨k, hk, hf⟩, hxf⟩
      rw [heq]
      exact (hM k hk).2.1 x hxk
    · intro x hx f hf hxf
      obtain ⟨k, hk, hf⟩ := mem_biUnion.mp hf
      have := mode_vert' (hM k hk) hf hxf
      apply hx
      rcases mem_union.mp this with h | h
      · exact mem_union_left _ (mem_biUnion.mpr ⟨k, hk, h⟩)
      · exact mem_union_right _ (mem_inter.mp h).1
  · intro w hw
    obtain ⟨k, hk, hw⟩ := mem_biUnion.mp hw
    exact hWc k hk hw

end S07V27
