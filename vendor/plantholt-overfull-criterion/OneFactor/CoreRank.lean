/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Pivot

/-!
# Adding the core edges in order (Chetwynd–Hilton 1989, Theorems 4–5)

`colorable_of_rank`: all degrees are at most `k`, the vertices of degree `k` lie in `S`, and the
edges inside `S` are ranked injectively. If every edge `xy` inside `S` has an end `x` (the pivot)
such that each other neighbour `z ∈ S` of `x` joined to it by an edge of smaller rank still has an
edge `zu` inside `S` of larger rank than `xy`, then `G` is `k`-edge-colourable: colour `G` minus
the edges inside `S` by Fournier's theorem, then add the edges inside `S` by increasing rank with
the pivot lemma.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` without the edges inside `S` of rank at least `B`. -/
def lowPart (G : SimpleGraph V) (S : Finset V) (ρ : V → V → ℕ) (B : ℕ) : SimpleGraph V :=
  G.deleteEdges {e | ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∈ S ∧ B ≤ ρ a b}

theorem lowPart_adj {G : SimpleGraph V} {S : Finset V} {ρ : V → V → ℕ}
    (hsym : ∀ a b, ρ a b = ρ b a) {B : ℕ} {u v : V} :
    (lowPart G S ρ B).Adj u v ↔ G.Adj u v ∧ ¬ (u ∈ S ∧ v ∈ S ∧ B ≤ ρ u v) := by
  simp only [lowPart, deleteEdges_adj, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun ⟨hu, hv, hB⟩ => h' ⟨u, v, rfl, hu, hv, hB⟩⟩
  · rintro ⟨h, h'⟩
    refine ⟨h, fun ⟨a, b, he, ha, hb, hB⟩ => h' ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, hB⟩
    · exact ⟨hb, ha, hsym u v ▸ hB⟩

theorem degree_lt_of_le_of_not_adj {H G : SimpleGraph V} [DecidableRel H.Adj]
    [DecidableRel G.Adj] (h : H ≤ G) {z u : V} (hG : G.Adj z u) (hH : ¬ H.Adj z u) :
    H.degree z < G.degree z := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply card_lt_card
  refine ⟨fun v hv => (mem_neighborFinset _ _ _).2 (h ((mem_neighborFinset _ _ _).1 hv)),
    fun hsub => hH ((mem_neighborFinset _ _ _).1 (hsub ((mem_neighborFinset _ _ _).2 hG)))⟩

/-- **Adding the edges inside `S` by rank.** -/
theorem colorable_of_rank (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hmax : ∀ v, G.degree v ≤ k) (S : Finset V) (hS : ∀ v, v ∉ S → G.degree v < k)
    (ρ : V → V → ℕ) (hsym : ∀ a b, ρ a b = ρ b a) (Bm : ℕ)
    (hbd : ∀ a b, a ∈ S → b ∈ S → G.Adj a b → ρ a b < Bm)
    (hinj : ∀ a b c e, a ∈ S → b ∈ S → c ∈ S → e ∈ S → G.Adj a b → G.Adj c e →
      ρ a b = ρ c e → s(a, b) = s(c, e))
    (hpiv : ∀ a b, a ∈ S → b ∈ S → G.Adj a b → ∃ x y, s(x, y) = s(a, b) ∧
      ∀ z, z ∈ S → G.Adj x z → z ≠ y → ρ x z < ρ x y →
        ∃ u, u ∈ S ∧ G.Adj z u ∧ ρ x y < ρ z u) :
    G.lineGraph.Colorable k := by
  classical
  have hle : ∀ B, lowPart G S ρ B ≤ G := fun B => deleteEdges_le _
  have hmaxB : ∀ B v, (lowPart G S ρ B).degree v ≤ k := fun B v =>
    (degree_le_of_le (hle B)).trans (hmax v)
  have key : ∀ B, (lowPart G S ρ B).lineGraph.Colorable k := by
    intro B
    induction B with
    | zero =>
      refine colorable_of_full_indep _ _ le_rfl (hmaxB 0) fun u v huv hu => ?_
      by_contra hv
      push_neg at hv
      have hu' : u ∈ S := by
        by_contra h
        have := hS u h
        have := degree_le_of_le (G := lowPart G S ρ 0) (H := G) (v := u) (hle 0)
        omega
      have hv' : v ∈ S := by
        by_contra h
        have := hS v h
        have := degree_le_of_le (G := lowPart G S ρ 0) (H := G) (v := v) (hle 0)
        omega
      exact ((lowPart_adj hsym).1 huv).2 ⟨hu', hv', Nat.zero_le _⟩
    | succ B ih =>
      by_cases he : ∃ a b, a ∈ S ∧ b ∈ S ∧ G.Adj a b ∧ ρ a b = B
      · obtain ⟨a, b, ha, hb, hab, hρ⟩ := he
        obtain ⟨x, y, hxy, hp⟩ := hpiv a b ha hb hab
        have hxyS : x ∈ S ∧ y ∈ S ∧ G.Adj x y ∧ ρ x y = B := by
          rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨ha, hb, hab, hρ⟩
          · exact ⟨hb, ha, hab.symm, by rw [hsym]; exact hρ⟩
        obtain ⟨hx, hy, hxyG, hρxy⟩ := hxyS
        have hadj : (lowPart G S ρ (B + 1)).Adj x y :=
          (lowPart_adj hsym).2 ⟨hxyG, fun ⟨_, _, h⟩ => by omega⟩
        refine colorable_of_pivot _ (hmaxB (B + 1)) hadj ?_ fun z hz hzy => ?_
        · have heq : (lowPart G S ρ (B + 1)).deleteEdges {s(x, y)} = lowPart G S ρ B := by
            ext u v
            rw [deleteEdges_adj, lowPart_adj hsym, lowPart_adj hsym, Set.mem_singleton_iff]
            constructor
            · rintro ⟨⟨huv, h1⟩, h2⟩
              refine ⟨huv, fun ⟨hu, hv, hB⟩ => ?_⟩
              rcases Nat.lt_or_ge B (ρ u v) with hlt | hge
              · exact h1 ⟨hu, hv, hlt⟩
              · have hρuv : ρ u v = B := le_antisymm hge hB
                exact h2 (hinj u v x y hu hv hx hy huv hxyG (hρuv.trans hρxy.symm))
            · rintro ⟨huv, h1⟩
              refine ⟨⟨huv, fun ⟨hu, hv, hB⟩ => h1 ⟨hu, hv, by omega⟩⟩, fun he => ?_⟩
              have : ρ u v = ρ x y := by
                rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rfl
                · exact hsym _ _
              exact h1 ⟨by rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption,
                by rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption, by omega⟩
          rw [heq]; exact ih
        · obtain ⟨hzG, hnot⟩ := (lowPart_adj hsym).1 hz
          by_cases hzS : z ∈ S
          · have hρxz : ρ x z < ρ x y := by
              have h1 : ρ x z < B + 1 := by
                by_contra h; exact hnot ⟨hx, hzS, by omega⟩
              have h2 : ρ x z ≠ B := fun h => by
                have := hinj x z x y hx hzS hx hy hzG hxyG (h.trans hρxy.symm)
                rcases Sym2.eq_iff.1 this with ⟨-, h3⟩ | ⟨h3, h4⟩
                · exact hzy h3
                · exact hzy (h4.trans h3)
              omega
            obtain ⟨u, hu, hzu, hlt⟩ := hp z hzS hzG hzy hρxz
            have hnu : ¬ (lowPart G S ρ (B + 1)).Adj z u := fun h =>
              ((lowPart_adj hsym).1 h).2 ⟨hzS, hu, by omega⟩
            exact (degree_lt_of_le_of_not_adj (hle _) hzu hnu).trans_le (hmax z)
          · exact (degree_le_of_le (hle _)).trans_lt (hS z hzS)
      · push_neg at he
        have heq : lowPart G S ρ (B + 1) = lowPart G S ρ B := by
          ext u v
          rw [lowPart_adj hsym, lowPart_adj hsym]
          constructor
          · rintro ⟨huv, h1⟩
            refine ⟨huv, fun ⟨hu, hv, hB⟩ => h1 ⟨hu, hv, ?_⟩⟩
            rcases Nat.lt_or_ge B (ρ u v) with hlt | hge
            · omega
            · exact absurd (le_antisymm hge hB) (he u v hu hv huv)
          · rintro ⟨huv, h1⟩
            exact ⟨huv, fun ⟨hu, hv, hB⟩ => h1 ⟨hu, hv, by omega⟩⟩
        rw [heq]; exact ih
  have hfull : lowPart G S ρ Bm = G := by
    ext u v
    rw [lowPart_adj hsym]
    constructor
    · exact fun h => h.1
    · intro huv
      exact ⟨huv, fun ⟨hu, hv, hB⟩ => by have := hbd u v hu hv huv; omega⟩
  have := key Bm
  rw [hfull] at this
  convert this

end OneFactor
