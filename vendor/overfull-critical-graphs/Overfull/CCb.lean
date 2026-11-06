/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.CCa

/-!
# Chen–Cao Theorem 1.3 (variant): Case 2

At most one small vertex and `G` not overfull: the Parity Lemma gives two vertices `x, y` of degree
in `[Δ − k + 1, Δ − 1]` missing colours of `A` (after possibly one Kempe change), and a short kite
on `a b cc u x y` contradicts `BroomProp`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A colouring of `G − ab` gives the data of the proof. -/
theorem MainSetupCC.of_colouring (hG : IsDeltaCritical G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {k : ℕ} (hda : G.degree a = k) (hmin : ∀ v, k ≤ G.degree v)
    (hdb : G.degree b = G.maxDegree) (hcond : 2 * Fintype.card V + 5 * k ≤ 3 * G.maxDegree + 6) :
    ∃ cc β, MainSetupCC G c a b cc k β := by
  have hmb := hcm.card_missing_end (Or.inr rfl)
  rw [hdb] at hmb
  obtain ⟨β, hβ⟩ := card_pos.1 (show 0 < #(missing c b) by omega)
  rw [mem_missing] at hβ
  have hβa : ¬ c.IsFree a β := fun h => (hcm.ab_facts hG.2.1).1 β h hβ
  simp only [IsFree, not_forall, not_not] at hβa
  obtain ⟨cc, hcc⟩ := hβa
  exact ⟨cc, β, hG, hcm, hda, hmin, hdb, hβ, hcc, hcond⟩

namespace MainSetupCC

variable {c : PEC G (Fin G.maxDegree)} {a b cc : V} {k : ℕ} {β : Fin G.maxDegree}
  (S : MainSetupCC G c a b cc k β)
include S

theorem lt_max_of_free {v : V} (hva : v ≠ a) (hvb : v ≠ b) {θ : Fin G.maxDegree}
    (h : c.IsFree v θ) : G.degree v < G.maxDegree := by
  have := S.cm.card_missing_other hva hvb
  have : 0 < #(missing c v) := card_pos.2 ⟨θ, mem_missing.2 h⟩
  omega

/-- Two vertices of degree `≥ Δ − k + 1` missing colours of `A` cannot be distinct. -/
theorem ne_of_two {x : V} (hxa : x ≠ a) (hxb : x ≠ b) (hx : G.maxDegree + 1 ≤ G.degree x + k)
    {θ₁ θ₂ : Fin G.maxDegree} (hne : θ₁ ≠ θ₂) (h₁ : InA c a b θ₁) (h₂ : InA c a b θ₂)
    (hx₁ : c.IsFree x θ₁) (hx₂ : c.IsFree x θ₂) : False := by
  refine no_two_inA S.crit S.cm S.db hxa hxb ?_ hne h₁ h₂ hx₁ hx₂
  have := S.hcond
  have := S.k2
  rw [S.da]
  split_ifs <;> omega

/-- **The core of Case 2.** Two distinct vertices `x, y ∉ {a, b}` of degree in `[Δ − k + 1, Δ − 1]`,
each missing a colour of `A`, contradict `BroomProp`. -/
theorem core (hSK : BroomProp G) {x y : V} (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b) (hx : G.maxDegree + 1 ≤ G.degree x + k)
    (hy : G.maxDegree + 1 ≤ G.degree y + k) (hxΔ : G.degree x < G.maxDegree)
    (hyΔ : G.degree y < G.maxDegree) (hθx : ∃ θ, InA c a b θ ∧ c.IsFree x θ)
    (hθy : ∃ θ, InA c a b θ ∧ c.IsFree y θ) : False := by
  obtain ⟨u, hua, hux, huy, hub, gx, gy, ⟨δ, hδ, hδA⟩⟩ := S.count3 ⟨hxa, hx⟩ ⟨hya, hy⟩
  refine hSK c a b u x y ?_ S.cm ⟨δ, hδ, S.free_a_of_good_b hδ hδA⟩ (good_symm.1 gx)
    (good_symm.1 gy) hθx hθy
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or]
  exact ⟨⟨S.cm.adj.ne, hua.symm, hxa.symm, hya.symm⟩, ⟨hub.symm, hxb.symm, hyb.symm⟩,
    ⟨hux, huy⟩, hxy, not_false⟩

open Classical in
/-- A colour of `A` not missing at `t` and missing at an even/odd number of vertices with the right
count is missing at some vertex outside `{a, b, t}`. -/
theorem exists_other_free {θ : Fin G.maxDegree} (hA : InA c a b θ) {t : V}
    (hcard : 2 ≤ #(univ.filter fun v => c.IsFree v θ))
    (hcard3 : c.IsFree t θ → 3 ≤ #(univ.filter fun v => c.IsFree v θ)) :
    ∃ v, v ≠ a ∧ v ≠ b ∧ v ≠ t ∧ c.IsFree v θ := by
  obtain ⟨hdis, -⟩ := S.cm.ab_facts S.crit.2.1
  set F := univ.filter fun v => c.IsFree v θ with hF
  have hsub : F ⊆ ((F.erase a).erase b).erase t ∪ {a, b, t} := by
    intro v hv
    by_cases h1 : v = a
    · exact mem_union_right _ (by simp [h1])
    by_cases h2 : v = b
    · exact mem_union_right _ (by simp [h2])
    by_cases h3 : v = t
    · exact mem_union_right _ (by simp [h3])
    exact mem_union_left _ (mem_erase.2 ⟨h3, mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, hv⟩⟩⟩)
  -- at most one of `a, b` lies in `F`, and `t` only if `F` is large
  have hab : ¬ (a ∈ F ∧ b ∈ F) := by
    rintro ⟨ha, hb⟩
    simp only [hF, mem_filter, mem_univ, true_and] at ha hb
    exact hdis θ ha hb
  have hsub' : F ∩ {a, b, t} ⊆ F ∩ {a, b, t} := subset_rfl
  have hcover : F ⊆ ((F.erase a).erase b).erase t ∪ (F ∩ {a, b, t}) := by
    intro v hv
    rcases mem_union.1 (hsub hv) with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_inter.2 ⟨hv, h⟩)
  have hsmall : #(F ∩ {a, b, t}) + 1 ≤ #F := by
    by_cases ht : t ∈ F
    · have h3 := hcard3 (by simpa [hF] using ht)
      have : #(F ∩ {a, b, t}) ≤ 2 := by
        rcases not_and_or.1 hab with h | h
        · have : F ∩ {a, b, t} ⊆ {b, t} := by
            intro v hv
            simp only [mem_inter, mem_insert, mem_singleton] at hv ⊢
            rcases hv.2 with rfl | rfl | rfl
            · exact absurd hv.1 h
            · exact Or.inl rfl
            · exact Or.inr rfl
          exact (card_le_card this).trans card_le_two
        · have : F ∩ {a, b, t} ⊆ {a, t} := by
            intro v hv
            simp only [mem_inter, mem_insert, mem_singleton] at hv ⊢
            rcases hv.2 with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact absurd hv.1 h
            · exact Or.inr rfl
          exact (card_le_card this).trans card_le_two
      omega
    · have : #(F ∩ {a, b, t}) ≤ 1 := by
        rcases not_and_or.1 hab with h | h
        · have : F ∩ {a, b, t} ⊆ {b} := by
            intro v hv
            simp only [mem_inter, mem_insert, mem_singleton] at hv ⊢
            rcases hv.2 with rfl | rfl | rfl
            · exact absurd hv.1 h
            · rfl
            · exact absurd hv.1 ht
          exact (card_le_card this).trans (by simp)
        · have : F ∩ {a, b, t} ⊆ {a} := by
            intro v hv
            simp only [mem_inter, mem_insert, mem_singleton] at hv ⊢
            rcases hv.2 with rfl | rfl | rfl
            · rfl
            · exact absurd hv.1 h
            · exact absurd hv.1 ht
          exact (card_le_card this).trans (by simp)
      omega
  have := (card_le_card hcover).trans (card_union_le _ _)
  obtain ⟨v, hv⟩ := card_pos.1 (show 0 < #(((F.erase a).erase b).erase t) by omega)
  simp only [mem_erase, hF, mem_filter, mem_univ, true_and] at hv
  exact ⟨v, hv.2.2.1, hv.2.1, hv.1, hv.2.2.2⟩

end MainSetupCC

end Overfull
