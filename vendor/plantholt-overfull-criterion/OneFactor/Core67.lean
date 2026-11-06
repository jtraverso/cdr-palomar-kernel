/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.CoreRank
public import OneFactor.Pair67

/-!
# The core left after the staircase (Chetwynd–Hilton 1989, Theorem 5)

`core_colorable`: after the staircase factors are removed, the edges inside `HV` are of three
kinds: between right vertices, `l r` with `idx l < idx r` (the graph `B`), and the matching edges
`l r` with `idx l = idx r` (the trees). Adding them in this order (right–right edges with both ends
matched, right–right edges at an unmatched vertex, `B`, the matching by increasing index) keeps a
pivot without full neighbours at each step, since the matching edges come last.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A symmetric injective code of pairs. -/
noncomputable def pcode (u v : V) : ℕ := (Fintype.equivFin (Sym2 V) s(u, v) : ℕ)

theorem pcode_symm (u v : V) : pcode u v = pcode v u := by
  unfold pcode; rw [Sym2.eq_swap]

theorem pcode_lt (u v : V) : pcode u v < Fintype.card (Sym2 V) :=
  (Fintype.equivFin (Sym2 V) s(u, v)).isLt

theorem pcode_inj {a b c e : V} (h : pcode a b = pcode c e) : s(a, b) = s(c, e) :=
  (Fintype.equivFin (Sym2 V)).injective (Fin.ext h)

/-- **The core after the staircase is colourable.** -/
theorem core_colorable {HS HV : Finset V} (D : StairData HS) (hHV : HV ⊆ HS) (M G₁ : SimpleGraph V)
    [DecidableRel G₁.Adj] {k : ℕ} (hmax : ∀ v, G₁.degree v ≤ k) (hS : ∀ v, v ∉ HV → G₁.degree v < k)
    (hMG : M ≤ G₁) (hM : IsMatchingGraph M)
    (hsideM : ∀ u v, M.Adj u v → u ∈ HV ∧ v ∈ HV ∧ D.idx u = D.idx v ∧ D.side u ≠ D.side v)
    (hadjM : ∀ l r, l ∈ HV → r ∈ HV → D.side l = true → D.side r = false → D.idx l = D.idx r →
      M.Adj l r)
    (hRpos : ∀ v ∈ HV, D.side v = false → 1 ≤ D.idx v → v ∈ cover M)
    (hunm : ∀ v ∈ HV, v ∉ cover M → D.side v = false ∧ D.idx v ≤ 0)
    (hind : ∀ u v, u ∈ HV → v ∈ HV → G₁.Adj u v → u ∈ cover M ∨ v ∈ cover M)
    (hkind : ∀ u v, u ∈ HV → v ∈ HV → G₁.Adj u v →
      (D.side u = false ∧ D.side v = false) ∨ (D.side u = true ∧ D.side v = false ∧ D.idx u ≤ D.idx v) ∨
        (D.side u = false ∧ D.side v = true ∧ D.idx v ≤ D.idx u)) :
    G₁.lineGraph.Colorable k := by
  set K := Fintype.card (Sym2 V)
  let ρ : V → V → ℕ := fun u v =>
    if D.side u = false ∧ D.side v = false then
      (if u ∈ cover M ∧ v ∈ cover M then pcode u v else K + pcode u v)
    else if M.Adj u v then 3 * K + (D.idx u).toNat else 2 * K + pcode u v
  have hρRR : ∀ u v, D.side u = false → D.side v = false →
      ρ u v = if u ∈ cover M ∧ v ∈ cover M then pcode u v else K + pcode u v := fun u v hu hv => by
    simp only [ρ, hu, hv, and_self, if_true]
  have hρM : ∀ u v, M.Adj u v → ρ u v = 3 * K + (D.idx u).toNat := fun u v h => by
    have := hsideM u v h
    have hns : ¬ (D.side u = false ∧ D.side v = false) := by
      rintro ⟨h1, h2⟩; exact this.2.2.2 (h1.trans h2.symm)
    simp only [ρ, if_neg hns, if_pos h]
  have hρB : ∀ u v, ¬ (D.side u = false ∧ D.side v = false) → ¬ M.Adj u v →
      ρ u v = 2 * K + pcode u v := fun u v h1 h2 => by
    simp only [ρ, if_neg h1, if_neg h2]
  have hsym : ∀ a b, ρ a b = ρ b a := by
    intro a b
    by_cases h1 : D.side a = false ∧ D.side b = false
    · rw [hρRR a b h1.1 h1.2, hρRR b a h1.2 h1.1, pcode_symm]
      simp only [and_comm]
    · have h1' : ¬ (D.side b = false ∧ D.side a = false) := fun h => h1 ⟨h.2, h.1⟩
      by_cases h2 : M.Adj a b
      · rw [hρM a b h2, hρM b a h2.symm, (hsideM a b h2).2.2.1]
      · rw [hρB a b h1 h2, hρB b a h1' (fun h => h2 h.symm), pcode_symm]
  -- the idx of a vertex of `HV`
  have hidx : ∀ v ∈ HV, D.idx v ≤ D.m + 1 := fun v hv => by
    cases hs : D.side v
    · have := D.hR v (hHV hv) hs; omega
    · have := D.hL v (hHV hv) hs; omega
  have hidxM : ∀ u v, M.Adj u v → 1 ≤ D.idx u := fun u v h => by
    obtain ⟨hu, hv, he, hne⟩ := hsideM u v h
    cases hs : D.side u
    · have hsv : D.side v = true := by
        cases hsv : D.side v
        · exact absurd (hs.trans hsv.symm) hne
        · rfl
      have := D.hL v (hHV hv) hsv; omega
    · have := D.hL u (hHV hu) hs; omega
  refine colorable_of_rank G₁ hmax HV hS ρ hsym (3 * K + D.m.toNat + 2) ?_ ?_ ?_
  · -- bound
    intro a b ha hb hab
    have := pcode_lt a b
    by_cases h1 : D.side a = false ∧ D.side b = false
    · rw [hρRR a b h1.1 h1.2]; split_ifs <;> omega
    · by_cases h2 : M.Adj a b
      · rw [hρM a b h2]
        have := hidx a ha
        have := hidxM a b h2
        omega
      · rw [hρB a b h1 h2]; omega
  · -- injectivity
    intro a b c e ha hb hc he hab hce hρ
    have p1 := pcode_lt a b
    have p2 := pcode_lt c e
    by_cases h1 : D.side a = false ∧ D.side b = false <;>
      by_cases h1' : D.side c = false ∧ D.side e = false
    · rw [hρRR a b h1.1 h1.2, hρRR c e h1'.1 h1'.2] at hρ
      split_ifs at hρ <;> first | exact pcode_inj (by omega) | omega
    · rw [hρRR a b h1.1 h1.2] at hρ
      by_cases h2' : M.Adj c e
      · rw [hρM c e h2'] at hρ; split_ifs at hρ <;> omega
      · rw [hρB c e h1' h2'] at hρ; split_ifs at hρ <;> omega
    · rw [hρRR c e h1'.1 h1'.2] at hρ
      by_cases h2 : M.Adj a b
      · rw [hρM a b h2] at hρ; split_ifs at hρ <;> omega
      · rw [hρB a b h1 h2] at hρ; split_ifs at hρ <;> omega
    · by_cases h2 : M.Adj a b <;> by_cases h2' : M.Adj c e
      · rw [hρM a b h2, hρM c e h2'] at hρ
        have i1 := hidxM a b h2
        have i2 := hidxM c e h2'
        have hie : D.idx a = D.idx c := by omega
        -- the left ends coincide, hence so do the edges
        obtain ⟨-, -, hab', hsab⟩ := hsideM a b h2
        obtain ⟨-, -, hce', hsce⟩ := hsideM c e h2'
        have key : ∀ x y, M.Adj x y → ∃ l r, M.Adj l r ∧ s(l, r) = s(x, y) ∧ D.side l = true ∧
            D.idx l = D.idx x := by
          intro x y hxy
          obtain ⟨-, -, hxy', hsxy⟩ := hsideM x y hxy
          cases hsx : D.side x
          · have hsy : D.side y = true := by
              cases hsy : D.side y
              · exact absurd (hsx.trans hsy.symm) hsxy
              · rfl
            exact ⟨y, x, hxy.symm, Sym2.eq_swap, hsy, hxy'.symm⟩
          · exact ⟨x, y, hxy, rfl, hsx, rfl⟩
        obtain ⟨l1, r1, hl1, he1, hs1, hi1⟩ := key a b h2
        obtain ⟨l2, r2, hl2, he2, hs2, hi2⟩ := key c e h2'
        have hl1H := (hsideM l1 r1 hl1).1
        have hl2H := (hsideM l2 r2 hl2).1
        have hll : l1 = l2 := D.injL l1 (hHV hl1H) l2 (hHV hl2H) hs1 hs2 (by omega)
        subst hll
        have hrr : r1 = r2 := hM l1 r1 r2 hl1 hl2
        subst hrr
        rw [← he1, ← he2]
      · rw [hρM a b h2, hρB c e h1' h2'] at hρ
        have := hidxM a b h2
        omega
      · rw [hρB a b h1 h2, hρM c e h2'] at hρ
        have := hidxM c e h2'
        omega
      · rw [hρB a b h1 h2, hρB c e h1' h2'] at hρ
        exact pcode_inj (by omega)
  · -- pivots
    intro a b ha hb hab
    -- a matched right vertex has its matching edge, of top rank
    have hwit : ∀ z, z ∈ HV → z ∈ cover M → ∀ B : ℕ, B < 3 * K + (D.idx z).toNat →
        ∃ u, u ∈ HV ∧ G₁.Adj z u ∧ B < ρ z u := by
      intro z hz hc B hB
      obtain ⟨u, hu⟩ := mem_cover.1 hc
      exact ⟨u, (hsideM z u hu).2.1, hMG hu, by rw [hρM z u hu]; exact hB⟩
    rcases hkind a b ha hb hab with ⟨hsa, hsb⟩ | ⟨hsa, hsb, hle⟩ | ⟨hsa, hsb, hle⟩
    · -- right–right
      rcases hind a b ha hb hab with hca | hca
      · by_cases hcb : b ∈ cover M
        · -- both matched: pivot `a`
          refine ⟨a, b, rfl, fun z hz haz hzb hlt => ?_⟩
          rw [hρRR a b hsa hsb, if_pos ⟨hca, hcb⟩] at hlt
          have hsz : D.side z = false := by
            by_contra h
            have h' : D.side z = true := by simpa using h
            have hns : ¬ (D.side a = false ∧ D.side z = false) := fun h => by rw [h'] at h; simp at h
            by_cases hm : M.Adj a z
            · rw [hρM a z hm] at hlt; have := pcode_lt a b; omega
            · rw [hρB a z hns hm] at hlt; have := pcode_lt a b; omega
          have hcz : z ∈ cover M := by
            by_contra hcz
            rw [hρRR a z hsa hsz, if_neg (fun h => hcz h.2)] at hlt
            have := pcode_lt a b; omega
          have := pcode_lt a b
          rw [hρRR a b hsa hsb, if_pos ⟨hca, hcb⟩]
          exact hwit z hz hcz _ (by omega)
        · -- `b` unmatched: pivot `b`
          refine ⟨b, a, Sym2.eq_swap, fun z hz hbz hza hlt => ?_⟩
          have hsz : D.side z = false := by
            rcases hkind b z hb hz hbz with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨-, h, h'⟩
            · exact h
            · rw [hsb] at h; exact absurd h (by simp)
            · have := (hunm b hb hcb).2
              have := D.hL z (hHV hz) (by simpa using h)
              omega
          have hcz : z ∈ cover M := (hind b z hb hz hbz).resolve_left hcb
          rw [hρRR b a hsb hsa, if_neg (fun h => hcb h.1)]
          have := pcode_lt b a
          exact hwit z hz hcz _ (by omega)
      · -- `b` matched, `a` possibly unmatched: symmetric
        by_cases hcaM : a ∈ cover M
        · refine ⟨b, a, Sym2.eq_swap, fun z hz hbz hza hlt => ?_⟩
          rw [hρRR b a hsb hsa, if_pos ⟨hca, hcaM⟩] at hlt
          have hsz : D.side z = false := by
            by_contra h
            have h' : D.side z = true := by simpa using h
            have hns : ¬ (D.side b = false ∧ D.side z = false) := fun h => by rw [h'] at h; simp at h
            by_cases hm : M.Adj b z
            · rw [hρM b z hm] at hlt; have := pcode_lt b a; omega
            · rw [hρB b z hns hm] at hlt; have := pcode_lt b a; omega
          have hcz : z ∈ cover M := by
            by_contra hcz
            rw [hρRR b z hsb hsz, if_neg (fun h => hcz h.2)] at hlt
            have := pcode_lt b a; omega
          have := pcode_lt b a
          rw [hρRR b a hsb hsa, if_pos ⟨hca, hcaM⟩]
          exact hwit z hz hcz _ (by omega)
        · refine ⟨a, b, rfl, fun z hz haz hzb hlt => ?_⟩
          have hsz : D.side z = false := by
            rcases hkind a z ha hz haz with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨-, h, h'⟩
            · exact h
            · rw [hsa] at h; exact absurd h (by simp)
            · have := (hunm a ha hcaM).2
              have := D.hL z (hHV hz) (by simpa using h)
              omega
          have hcz : z ∈ cover M := (hind a z ha hz haz).resolve_left hcaM
          rw [hρRR a b hsa hsb, if_neg (fun h => hcaM h.1)]
          have := pcode_lt a b
          exact hwit z hz hcz _ (by omega)
    · -- `a ∈ L`, `b ∈ R`, `idx a ≤ idx b`: pivot `a`
      refine ⟨a, b, rfl, fun z hz haz hzb hlt => ?_⟩
      have hns : ∀ y, ¬ (D.side a = false ∧ D.side y = false) := fun y h => by
        rw [hsa] at h; simp at h
      -- `z` is a right vertex with `idx a ≤ idx z`
      have hz' : D.side z = false ∧ D.idx a ≤ D.idx z := by
        rcases hkind a z ha hz haz with ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -, -⟩
        · rw [hsa] at h; exact absurd h (by simp)
        · exact ⟨h1, h2⟩
        · rw [hsa] at h; exact absurd h (by simp)
      have hia := D.hL a (hHV ha) hsa
      have hcz : z ∈ cover M := hRpos z hz hz'.1 (by omega)
      -- `a z` is not the matching edge of `a` unless `z = b`
      have hrank : ρ a z < 3 * K + (D.idx z).toNat ∧ ρ a b < 3 * K + (D.idx z).toNat := by
        by_cases hmab : M.Adj a b
        · have hmz : ¬ M.Adj a z := fun h => hzb (hM a z b h hmab)
          rw [hρB a z (hns z) hmz, hρM a b hmab]
          rw [hρM a b hmab, hρB a z (hns z) hmz] at hlt
          have := pcode_lt a z
          refine ⟨by omega, ?_⟩
          -- `idx a < idx z`: otherwise `a z` would be a matching edge
          have hne : D.idx a ≠ D.idx z := fun e => hmz (hadjM a z ha hz hsa hz'.1 e)
          omega
        · have hmz : ¬ M.Adj a z := by
            intro h
            rw [hρM a z h, hρB a b (hns b) hmab] at hlt
            have := pcode_lt a b; omega
          have := pcode_lt a z
          have := pcode_lt a b
          rw [hρB a z (hns z) hmz, hρB a b (hns b) hmab]
          omega
      exact hwit z hz hcz _ hrank.2
    · -- `b ∈ L`, `a ∈ R`: pivot `b`
      refine ⟨b, a, Sym2.eq_swap, fun z hz hbz hza hlt => ?_⟩
      have hns : ∀ y, ¬ (D.side b = false ∧ D.side y = false) := fun y h => by
        rw [hsb] at h; simp at h
      have hz' : D.side z = false ∧ D.idx b ≤ D.idx z := by
        rcases hkind b z hb hz hbz with ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -, -⟩
        · rw [hsb] at h; exact absurd h (by simp)
        · exact ⟨h1, h2⟩
        · rw [hsb] at h; exact absurd h (by simp)
      have hib := D.hL b (hHV hb) hsb
      have hcz : z ∈ cover M := hRpos z hz hz'.1 (by omega)
      have hrank : ρ b a < 3 * K + (D.idx z).toNat := by
        by_cases hmba : M.Adj b a
        · have hmz : ¬ M.Adj b z := fun h => hza (hM b z a h hmba)
          rw [hρM b a hmba, hρB b z (hns z) hmz] at hlt
          rw [hρM b a hmba]
          have hne : D.idx b ≠ D.idx z := fun e => hmz (hadjM b z hb hz hsb hz'.1 e)
          omega
        · have := pcode_lt b a
          rw [hρB b a (hns a) hmba]
          omega
      exact hwit z hz hcz _ hrank

end OneFactor
