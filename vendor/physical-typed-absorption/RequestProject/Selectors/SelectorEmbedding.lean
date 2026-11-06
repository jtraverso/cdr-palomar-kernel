/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.RobustPaths
public import RequestProject.Selectors.SubdivBridge

@[expose] public section

/-!
# Constructed odd subdivisions of the parity and balanced selectors in a link

The embedding is constructed (by `SelEmbed.greedy_embedding`) BEFORE any mode, from explicit
density inputs on the physical link graph `linkGraph G v`; afterwards every mode of the
selector gives the exact positive partition with the one fuel fixed by the embedding.

* PAR (`parity_selector_embedding`): active set `A`; prescribed injective ports
  `ψ : Fin r → A \ Z0`; candidate sets `Cand x ⊆ A`.  Budget `B = |Z0| + 11 r`
  (`|PV r| = 3r`, `≤ 4r` edges, path length `≤ 3`).  Inputs: every `a ∈ A` has
  `≥ B + 2` link-neighbours in `A`, every two distinct `x, b ∈ A` have `≥ B + 2` common
  link-neighbours in `A`, `|Cand x| ≥ |Z0| + 3r`.
* BAL (`balanced_selector_embedding`): sides `X`, `Y` of the link; left vertices of the
  balanced selector go to `X`, right ones to `Y`; budget `B = |Z0| + 410 k`, `k = max l r`.
  Inputs: degrees across sides and same-side common neighbourhoods `≥ B + 2`,
  `|Cand x| ≥ |Z0| + 10 k`.

The bridge from H3–H4 to these density inputs is NOT proved here.
-/

namespace SelEmbed

open Finset SelSubdiv SelBridge ParitySel SelBalanced

variable {V : Type*} [DecidableEq V]

instance linkGraph_decRel (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (linkGraph G v).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ G.Adj v x ∧ G.Adj v y))

lemma card_PV (r : ℕ) : Fintype.card (PV r) = 3 * r := by
  simp [PV, Fintype.card_sum]; ring

lemma card_BV_le (l r : ℕ) : Fintype.card (BV l r) ≤ 10 * max l r := by
  simp only [BV, Fintype.card_sum, Fintype.card_fin]
  have := le_max_left l r; have := le_max_right l r
  omega

lemma not_isDiag_of_mem {β : Type*} {Γ : SimpleGraph β} [Fintype Γ.edgeSet] :
    ∀ e ∈ Γ.edgeFinset, ¬ e.IsDiag :=
  fun _ he => SimpleGraph.not_isDiag_of_mem_edgeSet _ (SimpleGraph.mem_edgeFinset.mp he)

/-- **PAR: constructed odd subdivision of the parity selector, then all even modes.** -/
theorem parity_selector_embedding (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (A Z0 : Finset V) (r : ℕ)
    (hdeg : ∀ a ∈ A, Z0.card + 11 * r + 2 ≤ (A.filter ((linkGraph G v).Adj a)).card)
    (hcom : ∀ x ∈ A, ∀ b ∈ A, x ≠ b → Z0.card + 11 * r + 2 ≤
      (A.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (ψ : Fin r → V) (hψ : Function.Injective ψ) (hψA : ∀ i, ψ i ∈ A) (hψZ : ∀ i, ψ i ∉ Z0)
    (Cand : PV r → Finset V) (hCA : ∀ x, Cand x ⊆ A)
    (hCand : ∀ x, Z0.card + 3 * r ≤ (Cand x).card) :
    ∃ D : OddSubdivision (linkGraph G v) (paritySelector r).edgeFinset,
      (∀ i, D.φ (pu i) = ψ i) ∧ (∀ x ∈ auxSet r, D.φ x ∈ Cand x) ∧
      (∀ x, D.φ x ∉ Z0) ∧ (∀ y ∈ D.internals, y ∉ Z0) ∧
      (∀ e ∈ (paritySelector r).edgeFinset, 2 * D.t e + 1 ≤ 3) ∧
      D.pathEdges.card ≤ 12 * r ∧ D.internals.card ≤ 8 * r ∧
      ∀ S : Finset (Fin r), Even S.card →
        ∃ F : Finset (Sym2 (PV r)),
          IsMode (paritySelector r).edgeFinset (auxSet r) (portSet S) F ∧
          IsMode D.pathEdges (D.auxCover (auxSet r)) ((portSet S).image D.φ) (D.modeEdges F) ∧
          (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
          (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
          Disjoint (fuel v D.pathEdges (D.auxCover (auxSet r)))
            (radial v ((portSet S).image D.φ)) ∧
          fuel v D.pathEdges (D.auxCover (auxSet r)) ∪ radial v ((portSet S).image D.φ) =
            (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
          Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  set Q := (paritySelector r).edgeFinset
  have hQc : Q.card ≤ 4 * r := paritySelector_card_edgeFinset_le r
  let Ports : Finset (PV r) := univ.image pu
  let ψ' : PV r → V := Sum.elim ψ (fun _ => v)
  have hψ' : Set.InjOn ψ' Ports := by
    intro x hx y hy hxy
    simp only [Ports, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    simp only [ψ', Sum.elim_inl] at hxy
    rw [hψ hxy]
  have hPorts : ∀ x ∈ Ports, ∃ i, x = pu i := by
    intro x hx; obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact ⟨i, rfl⟩
  have hR := robust_par (linkGraph G v) A (Z0.card + 11 * r) hdeg hcom
  obtain ⟨D, hP, hC, hZ, hlen, hint⟩ := greedy_embedding (linkGraph G v) (ParAllowed A) hR Q
    not_isDiag_of_mem (fun _ a => a ∈ A) (fun _ _ _ _ _ a b hab ha hb => ⟨ha, hb, hab⟩)
    Ports ψ' hψ' (fun x hx => by obtain ⟨i, rfl⟩ := hPorts x hx; exact hψA i)
    Z0 (fun x hx => by obtain ⟨i, rfl⟩ := hPorts x hx; exact hψZ i)
    Cand (fun x _ a ha => hCA x ha) (fun x _ => by rw [card_PV]; exact hCand x)
    (by rw [card_PV]; omega)
  refine ⟨D, fun i => hP (pu i) (mem_image_of_mem _ (mem_univ i)), ?_, hZ, hint, hlen,
    ?_, ?_, fun S hS => OddSubdivision.parity_subdiv_positive_modes D S hS⟩
  · intro x hx
    apply hC
    intro hxP
    obtain ⟨i, rfl⟩ := hPorts x hxP
    simp [auxSet] at hx
  · have := OddSubdivision.pathEdges_card_le (D := D) hlen; omega
  · have := OddSubdivision.internals_card_le (D := D) hlen; omega

/-- Side constraint for the bipartite (BAL) placement. -/
def balSide {l r : ℕ} (X Y : Finset V) (x : BV l r) (a : V) : Prop :=
  (x.isLeft → a ∈ X) ∧ (x.isRight → a ∈ Y)

/-- Prescribed port images of the balanced selector. -/
def balPorts {l r : ℕ} (v : V) (ψL : Fin l → V) (ψR : Fin r → V) : BV l r → V
  | Sum.inl (Sum.inr p) => ψL p
  | Sum.inr (Sum.inr q) => ψR q
  | _ => v

/-- **BAL: constructed odd subdivision of a balanced selector respecting sides, then all
balanced modes.** -/
theorem balanced_selector_embedding {l r : ℕ} (QB : SimpleGraph (BV l r)) [DecidableRel QB.Adj]
    (hbip : ∀ u w, QB.Adj u w → (u.isLeft ∧ w.isRight) ∨ (u.isRight ∧ w.isLeft))
    (hE : QB.edgeFinset.card ≤ 200 * max l r)
    (hQB : ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
      ∃ Mt : QB.Subgraph, Mt.verts = ↑(activeVerts SL SR) ∧ Mt.IsMatching)
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (X Y Z0 : Finset V) (hXY : Disjoint X Y)
    (hdegX : ∀ a ∈ X, Z0.card + 410 * max l r + 2 ≤ (Y.filter ((linkGraph G v).Adj a)).card)
    (hdegY : ∀ a ∈ Y, Z0.card + 410 * max l r + 2 ≤ (X.filter ((linkGraph G v).Adj a)).card)
    (hcomX : ∀ x ∈ X, ∀ b ∈ X, x ≠ b → Z0.card + 410 * max l r + 2 ≤
      (Y.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (hcomY : ∀ x ∈ Y, ∀ b ∈ Y, x ≠ b → Z0.card + 410 * max l r + 2 ≤
      (X.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (ψL : Fin l → V) (ψR : Fin r → V) (hψL : Function.Injective ψL)
    (hψR : Function.Injective ψR) (hψLX : ∀ p, ψL p ∈ X) (hψRY : ∀ q, ψR q ∈ Y)
    (hψLZ : ∀ p, ψL p ∉ Z0) (hψRZ : ∀ q, ψR q ∉ Z0)
    (Cand : BV l r → Finset V) (hCX : ∀ x : BV l r, x.isLeft → Cand x ⊆ X)
    (hCY : ∀ x : BV l r, x.isRight → Cand x ⊆ Y)
    (hCand : ∀ x, Z0.card + 10 * max l r ≤ (Cand x).card) :
    ∃ D : OddSubdivision (linkGraph G v) QB.edgeFinset,
      (∀ p, D.φ (Sum.inl (Sum.inr p)) = ψL p) ∧ (∀ q, D.φ (Sum.inr (Sum.inr q)) = ψR q) ∧
      (∀ x ∈ OddSubdivision.auxB l r, D.φ x ∈ Cand x) ∧ (∀ x, balSide X Y x (D.φ x)) ∧
      (∀ x, D.φ x ∉ Z0) ∧ (∀ y ∈ D.internals, y ∉ Z0) ∧
      (∀ e ∈ QB.edgeFinset, 2 * D.t e + 1 ≤ 3) ∧
      D.pathEdges.card ≤ 600 * max l r ∧ D.internals.card ≤ 400 * max l r ∧
      ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
        ∃ F : Finset (Sym2 (BV l r)), IsMode QB.edgeFinset (OddSubdivision.auxB l r) (OddSubdivision.portsB SL SR) F ∧
          IsMode D.pathEdges (D.auxCover (OddSubdivision.auxB l r)) ((OddSubdivision.portsB SL SR).image D.φ)
            (D.modeEdges F) ∧
          (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
          (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
          Disjoint (fuel v D.pathEdges (D.auxCover (OddSubdivision.auxB l r)))
            (radial v ((OddSubdivision.portsB SL SR).image D.φ)) ∧
          fuel v D.pathEdges (D.auxCover (OddSubdivision.auxB l r)) ∪ radial v ((OddSubdivision.portsB SL SR).image D.φ) =
            (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
          Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  set Q := QB.edgeFinset
  let Ports : Finset (BV l r) := OddSubdivision.portsB univ univ
  have hPorts : ∀ x ∈ Ports, (∃ p, x = Sum.inl (Sum.inr p)) ∨ ∃ q, x = Sum.inr (Sum.inr q) := by
    intro x hx
    simp only [Ports, OddSubdivision.portsB, mem_union, mem_image, mem_univ, true_and] at hx
    rcases hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact Or.inl ⟨p, rfl⟩
    · exact Or.inr ⟨q, rfl⟩
  have hψ' : Set.InjOn (balPorts v ψL ψR) Ports := by
    intro x hx y hy hxy
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩ <;> rcases hPorts y hy with ⟨p', rfl⟩ | ⟨q', rfl⟩
    · simp only [balPorts] at hxy; rw [hψL hxy]
    · simp only [balPorts] at hxy
      exact absurd (hxy ▸ hψLX p) (disjoint_right.mp hXY (hψRY q'))
    · simp only [balPorts] at hxy
      exact absurd (hxy ▸ hψRY q) (disjoint_left.mp hXY (hψLX p'))
    · simp only [balPorts] at hxy; rw [hψR hxy]
  have hR := robust_bal (linkGraph G v) X Y hXY (Z0.card + 410 * max l r) hdegX hdegY hcomX hcomY
  have hside : ∀ e ∈ Q, ∀ x y, s(x, y) = e → ∀ a b, a ≠ b → balSide X Y x a →
      balSide X Y y b → BalAllowed X Y a b := by
    intro e he x y hxy a b _ ha hb
    rw [← hxy, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hbip x y he with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨ha.1 hx, hb.2 hy⟩
    · exact Or.inr ⟨ha.2 hx, hb.1 hy⟩
  have hψS : ∀ x ∈ Ports, balSide X Y x (balPorts v ψL ψR x) := by
    intro x hx
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨fun _ => hψLX p, fun h => by simp at h⟩
    · exact ⟨fun h => by simp at h, fun _ => hψRY q⟩
  have hψZ : ∀ x ∈ Ports, balPorts v ψL ψR x ∉ Z0 := by
    intro x hx
    rcases hPorts x hx with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact hψLZ p
    · exact hψRZ q
  have hCS : ∀ x ∉ Ports, ∀ a ∈ Cand x, balSide X Y x a := by
    intro x _ a ha
    exact ⟨fun h => hCX x h ha, fun h => hCY x h ha⟩
  have hk := card_BV_le l r
  obtain ⟨D, hP, hC, hZ, hlen, hint⟩ := greedy_embedding (linkGraph G v) (BalAllowed X Y) hR Q
    not_isDiag_of_mem (balSide X Y) hside Ports (balPorts v ψL ψR) hψ' hψS Z0 hψZ Cand hCS
    (fun x _ => le_trans (by omega) (hCand x)) (by omega)
  have hφS : ∀ x, balSide X Y x (D.φ x) := by
    intro x
    by_cases hx : x ∈ Ports
    · rw [hP x hx]; exact hψS x hx
    · exact hCS x hx _ (hC x hx)
  refine ⟨D, fun p => ?_, fun q => ?_, ?_, hφS, hZ, hint, hlen, ?_, ?_,
    fun SL SR hS => OddSubdivision.balanced_subdiv_positive_modes QB hQB D SL SR hS⟩
  · rw [hP _ (by simp [Ports, OddSubdivision.portsB])]; rfl
  · rw [hP _ (by simp [Ports, OddSubdivision.portsB])]; rfl
  · intro x hx
    exact hC x (fun hxP => disjoint_left.mp (OddSubdivision.portsB_disjoint univ univ) hxP hx)
  · have := OddSubdivision.pathEdges_card_le (D := D) hlen; omega
  · have := OddSubdivision.internals_card_le (D := D) hlen; omega

/-- **PAR with explicit `α`-dependence.**  If the link degrees and common neighbourhoods in
`A` are at least `α n`, candidate sets have size `≥ α n`, and
`|Z0| + 11 r + 2 ≤ α n`, the parity selector on `r` ports is embedded (and has all its even
modes) as in `parity_selector_embedding`. -/
theorem parity_selector_embedding_alpha (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (A Z0 : Finset V) (r n : ℕ) (α : ℝ)
    (hdeg : ∀ a ∈ A, α * n ≤ (A.filter ((linkGraph G v).Adj a)).card)
    (hcom : ∀ x ∈ A, ∀ b ∈ A, x ≠ b →
      α * n ≤ (A.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (hres : (Z0.card + 11 * r + 2 : ℝ) ≤ α * n)
    (ψ : Fin r → V) (hψ : Function.Injective ψ) (hψA : ∀ i, ψ i ∈ A) (hψZ : ∀ i, ψ i ∉ Z0)
    (Cand : PV r → Finset V) (hCA : ∀ x, Cand x ⊆ A) (hCand : ∀ x, α * n ≤ (Cand x).card) :
    ∃ D : OddSubdivision (linkGraph G v) (paritySelector r).edgeFinset,
      (∀ i, D.φ (pu i) = ψ i) ∧ (∀ x ∈ auxSet r, D.φ x ∈ Cand x) ∧
      (∀ x, D.φ x ∉ Z0) ∧ (∀ y ∈ D.internals, y ∉ Z0) ∧
      (∀ e ∈ (paritySelector r).edgeFinset, 2 * D.t e + 1 ≤ 3) ∧
      D.pathEdges.card ≤ 12 * r ∧ D.internals.card ≤ 8 * r ∧
      ∀ S : Finset (Fin r), Even S.card →
        ∃ F : Finset (Sym2 (PV r)),
          IsMode (paritySelector r).edgeFinset (auxSet r) (portSet S) F ∧
          IsMode D.pathEdges (D.auxCover (auxSet r)) ((portSet S).image D.φ) (D.modeEdges F) ∧
          (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
          (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
          Disjoint (fuel v D.pathEdges (D.auxCover (auxSet r)))
            (radial v ((portSet S).image D.φ)) ∧
          fuel v D.pathEdges (D.auxCover (auxSet r)) ∪ radial v ((portSet S).image D.φ) =
            (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
          Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  have cast : ∀ m : ℕ, α * n ≤ m → Z0.card + 11 * r + 2 ≤ m := fun m hm => by
    exact_mod_cast hres.trans hm
  refine parity_selector_embedding G v A Z0 r (fun a ha => cast _ (hdeg a ha))
    (fun x hx b hb hxb => cast _ (hcom x hx b hb hxb)) ψ hψ hψA hψZ Cand hCA
    (fun x => ?_)
  have := cast _ (hCand x); omega

open Classical in
/-- **BAL, existence form.**  For `k = max l r ≥ 1` there is a balanced selector (bipartite,
degree `≤ 60`, `≤ 200 k` edges, all balanced modes) AND, from the stated link inputs, an
actual odd subdivision of it in the link, chosen before any mode, giving every balanced mode
with one fuel. -/
theorem balanced_selector_exists_embedded (l r : ℕ) (hk : 1 ≤ max l r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (X Y Z0 : Finset V) (hXY : Disjoint X Y)
    (hdegX : ∀ a ∈ X, Z0.card + 410 * max l r + 2 ≤ (Y.filter ((linkGraph G v).Adj a)).card)
    (hdegY : ∀ a ∈ Y, Z0.card + 410 * max l r + 2 ≤ (X.filter ((linkGraph G v).Adj a)).card)
    (hcomX : ∀ x ∈ X, ∀ b ∈ X, x ≠ b → Z0.card + 410 * max l r + 2 ≤
      (Y.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (hcomY : ∀ x ∈ Y, ∀ b ∈ Y, x ≠ b → Z0.card + 410 * max l r + 2 ≤
      (X.filter (fun y => (linkGraph G v).Adj x y ∧ (linkGraph G v).Adj y b)).card)
    (ψL : Fin l → V) (ψR : Fin r → V) (hψL : Function.Injective ψL)
    (hψR : Function.Injective ψR) (hψLX : ∀ p, ψL p ∈ X) (hψRY : ∀ q, ψR q ∈ Y)
    (hψLZ : ∀ p, ψL p ∉ Z0) (hψRZ : ∀ q, ψR q ∉ Z0)
    (Cand : BV l r → Finset V) (hCX : ∀ x : BV l r, x.isLeft → Cand x ⊆ X)
    (hCY : ∀ x : BV l r, x.isRight → Cand x ⊆ Y)
    (hCand : ∀ x, Z0.card + 10 * max l r ≤ (Cand x).card) :
    ∃ QB : SimpleGraph (BV l r),
      (∀ u w, QB.Adj u w → (u.isLeft ∧ w.isRight) ∨ (u.isRight ∧ w.isLeft)) ∧
      QB.maxDegree ≤ 60 ∧ QB.edgeFinset.card ≤ 200 * max l r ∧
      ∃ D : OddSubdivision (linkGraph G v) QB.edgeFinset,
        (∀ p, D.φ (Sum.inl (Sum.inr p)) = ψL p) ∧ (∀ q, D.φ (Sum.inr (Sum.inr q)) = ψR q) ∧
        (∀ x ∈ OddSubdivision.auxB l r, D.φ x ∈ Cand x) ∧ (∀ x, balSide X Y x (D.φ x)) ∧
        (∀ x, D.φ x ∉ Z0) ∧ (∀ y ∈ D.internals, y ∉ Z0) ∧
        (∀ e ∈ QB.edgeFinset, 2 * D.t e + 1 ≤ 3) ∧
        D.pathEdges.card ≤ 600 * max l r ∧ D.internals.card ≤ 400 * max l r ∧
        ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
          ∃ F : Finset (Sym2 (BV l r)),
            IsMode QB.edgeFinset (OddSubdivision.auxB l r) (OddSubdivision.portsB SL SR) F ∧
            IsMode D.pathEdges (D.auxCover (OddSubdivision.auxB l r))
              ((OddSubdivision.portsB SL SR).image D.φ) (D.modeEdges F) ∧
            fuel v D.pathEdges (D.auxCover (OddSubdivision.auxB l r)) ∪
                radial v ((OddSubdivision.portsB SL SR).image D.φ) =
              (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
            Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  obtain ⟨QB, hbip, -, hmax, hE, hQB⟩ := balancedSelector_exists l r hk
  obtain ⟨D, h1, h2, h3, h4, h5, h6, h7, h8, h9, hmodes⟩ :=
    balanced_selector_embedding QB hbip (by convert hE) hQB G v X Y Z0 hXY hdegX hdegY hcomX
      hcomY ψL ψR hψL hψR hψLX hψRY hψLZ hψRZ Cand hCX hCY hCand
  refine ⟨QB, hbip, hmax, by convert hE, D, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  intro SL SR hS
  obtain ⟨F, a, b, -, -, -, c, d⟩ := hmodes SL SR hS
  exact ⟨F, a, b, c, d⟩

end SelEmbed
