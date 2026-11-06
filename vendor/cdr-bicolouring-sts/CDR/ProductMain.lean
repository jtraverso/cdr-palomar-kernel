/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Product

/-!
# Theorem 2.4 of Colbourn–Dinitz–Rosa: proofs

`prod_isSTS`: the product blocks form a Steiner triple system on `Fin v × Fin u`;
`prod_isBicolouring`: the colouring `φ p − ψ i` is a bicolouring;
`card_prodColour`: the colour classes have sizes `Σ_m |ψ-class m| · |φ-class (k + m)|`;
`bicolourable3_mul`: **Theorem 2.4**.
-/

@[expose] public section

namespace CDR

open Finset

variable {u v : ℕ}

/-! ### Coordinates in a cross triple -/

section Cross

variable {ψ : Fin v → Fin 3} {L₁ L₂ : Fin u → Fin u → Fin u} {f g h : Fin v}

theorem crossTriple_coord_f (hfg : f ≠ g) (hfh : f ≠ h) {r s p : Fin u}
    (hm : (f, p) ∈ crossTriple ψ L₁ L₂ f g h r s) : p = r := by
  rcases mem_crossTriple.1 hm with ⟨-, hp⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact hp
  · exact absurd h' hfg
  · exact absurd h' hfh

theorem crossTriple_coord_g (hfg : f ≠ g) (hgh : g ≠ h) {r s p : Fin u}
    (hm : (g, p) ∈ crossTriple ψ L₁ L₂ f g h r s) : p = s := by
  rcases mem_crossTriple.1 hm with ⟨h', -⟩ | ⟨-, hp⟩ | ⟨h', -⟩
  · exact absurd h'.symm hfg
  · exact hp
  · exact absurd h' hgh

theorem crossTriple_coord_h (hfh : f ≠ h) (hgh : g ≠ h) {r s p : Fin u}
    (hm : (h, p) ∈ crossTriple ψ L₁ L₂ f g h r s) : p = sel ψ L₁ L₂ f h r s := by
  rcases mem_crossTriple.1 hm with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hp⟩
  · exact absurd h'.symm hfh
  · exact absurd h'.symm hgh
  · exact hp

theorem crossTriple_first_mem {r s p : Fin u} {j : Fin v}
    (hm : (j, p) ∈ crossTriple ψ L₁ L₂ f g h r s) : j = f ∨ j = g ∨ j = h := by
  rcases mem_crossTriple.1 hm with ⟨hj, -⟩ | ⟨hj, -⟩ | ⟨hj, -⟩
  · exact Or.inl hj
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr hj)

/-- Two points with distinct first coordinates in a block of an oriented triple determine the
pair `(r, s)`. -/
theorem crossTriple_unique (hL : IsLatinSquare (sel ψ L₁ L₂ f h)) (hfg : f ≠ g) (hfh : f ≠ h)
    (hgh : g ≠ h) {i j : Fin v} {p q r s r' s' : Fin u} (hij : i ≠ j)
    (h1 : (i, p) ∈ crossTriple ψ L₁ L₂ f g h r s) (h2 : (j, q) ∈ crossTriple ψ L₁ L₂ f g h r s)
    (h1' : (i, p) ∈ crossTriple ψ L₁ L₂ f g h r' s')
    (h2' : (j, q) ∈ crossTriple ψ L₁ L₂ f g h r' s') : r = r' ∧ s = s' := by
  rcases crossTriple_first_mem h1 with rfl | rfl | rfl <;>
    rcases crossTriple_first_mem h2 with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact ⟨(crossTriple_coord_f hfg hfh h1).symm.trans (crossTriple_coord_f hfg hfh h1'),
      (crossTriple_coord_g hfg hgh h2).symm.trans (crossTriple_coord_g hfg hgh h2')⟩
  · have hr := (crossTriple_coord_f hfg hfh h1).symm.trans (crossTriple_coord_f hfg hfh h1')
    subst hr
    have := (crossTriple_coord_h hfh hgh h2).symm.trans (crossTriple_coord_h hfh hgh h2')
    exact ⟨rfl, (hL.1 r).1 this⟩
  · exact ⟨(crossTriple_coord_f hfg hfh h2).symm.trans (crossTriple_coord_f hfg hfh h2'),
      (crossTriple_coord_g hfg hgh h1).symm.trans (crossTriple_coord_g hfg hgh h1')⟩
  · exact absurd rfl hij
  · have hs := (crossTriple_coord_g hfg hgh h1).symm.trans (crossTriple_coord_g hfg hgh h1')
    subst hs
    have := (crossTriple_coord_h hfh hgh h2).symm.trans (crossTriple_coord_h hfh hgh h2')
    exact ⟨(hL.2 s).1 this, rfl⟩
  · have hr := (crossTriple_coord_f hfg hfh h2).symm.trans (crossTriple_coord_f hfg hfh h2')
    subst hr
    have := (crossTriple_coord_h hfh hgh h1).symm.trans (crossTriple_coord_h hfh hgh h1')
    exact ⟨rfl, (hL.1 r).1 this⟩
  · have hs := (crossTriple_coord_g hfg hgh h2).symm.trans (crossTriple_coord_g hfg hgh h2')
    subst hs
    have := (crossTriple_coord_h hfh hgh h1).symm.trans (crossTriple_coord_h hfh hgh h1')
    exact ⟨(hL.2 s).1 this, rfl⟩
  · exact absurd rfl hij

/-- Two points with distinct first coordinates among `f, g, h` lie in some cross triple. -/
theorem crossTriple_exists (hL : IsLatinSquare (sel ψ L₁ L₂ f h)) {i j : Fin v} {p q : Fin u}
    (hij : i ≠ j) (hi : i = f ∨ i = g ∨ i = h) (hj : j = f ∨ j = g ∨ j = h) :
    ∃ r s, (i, p) ∈ crossTriple ψ L₁ L₂ f g h r s ∧ (j, q) ∈ crossTriple ψ L₁ L₂ f g h r s := by
  simp only [mem_crossTriple]
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact ⟨p, q, by tauto, by tauto⟩
  · obtain ⟨s, hs⟩ := (hL.1 p).2 q
    exact ⟨p, s, by tauto, Or.inr (Or.inr ⟨rfl, hs.symm⟩)⟩
  · exact ⟨q, p, by tauto, by tauto⟩
  · exact absurd rfl hij
  · obtain ⟨r, hr⟩ := (hL.2 p).2 q
    exact ⟨r, p, by tauto, Or.inr (Or.inr ⟨rfl, hr.symm⟩)⟩
  · obtain ⟨s, hs⟩ := (hL.1 q).2 p
    exact ⟨q, s, Or.inr (Or.inr ⟨rfl, hs.symm⟩), by tauto⟩
  · obtain ⟨r, hr⟩ := (hL.2 q).2 p
    exact ⟨r, q, Or.inr (Or.inr ⟨rfl, hr.symm⟩), by tauto⟩
  · exact absurd rfl hij

end Cross

/-! ### Orientations exist -/

theorem exists_oriented {B₂ : Finset (Finset (Fin v))} {ψ : Fin v → Fin 3} (h₂ : IsSTS B₂)
    (hψ : IsBicolouring B₂ ψ) {T : Finset (Fin v)} (hT : T ∈ B₂) :
    ∃ f g h, Oriented B₂ ψ f g h ∧ ({f, g, h} : Finset (Fin v)) = T := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 (h₂.card_eq T hT)
  have himg := hψ _ hT
  rw [image_insert, image_insert, image_singleton] at himg
  have hT' : ∀ {a b c : Fin v}, ({a, b, c} : Finset (Fin v)) = {x, y, z} →
      {a, b, c} ∈ B₂ := fun h => h ▸ hT
  by_cases e1 : ψ x = ψ y <;> by_cases e2 : ψ x = ψ z
  · rw [e1, ← e1, e2] at himg
    simp at himg
  · rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨x, y, z, ⟨hT, hlt, e1, fun h => e2 h.symm⟩, rfl⟩
    · exact ⟨y, x, z, ⟨hT' (by rw [insert_comm]), hlt, e1.symm, fun h => e2 (e1.trans h.symm)⟩,
        by rw [insert_comm]⟩
  · rcases lt_or_gt_of_ne hxz with hlt | hlt
    · refine ⟨x, z, y, ⟨hT' ?_, hlt, e2, fun h => e1 h.symm⟩, ?_⟩ <;>
        · ext w; simp; tauto
    · refine ⟨z, x, y, ⟨hT' ?_, hlt, e2.symm, fun h => e1 (e2.trans h.symm)⟩, ?_⟩ <;>
        · ext w; simp; tauto
  · by_cases e3 : ψ y = ψ z
    · rcases lt_or_gt_of_ne hyz with hlt | hlt
      · refine ⟨y, z, x, ⟨hT' ?_, hlt, e3, e1⟩, ?_⟩ <;>
          · ext w; simp; tauto
      · refine ⟨z, y, x, ⟨hT' ?_, hlt, e3.symm, e2⟩, ?_⟩ <;>
          · ext w; simp; tauto
    · rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton] at himg
      · omega
      · simpa using e3
      · simp [e1, e2]


/-! ### The product is a Steiner triple system -/

section STS

variable {B₁ : Finset (Finset (Fin u))} {B₂ : Finset (Finset (Fin v))} {ψ : Fin v → Fin 3}
  {L₁ L₂ : Fin u → Fin u → Fin u}

theorem card_crossTriple (h₂ : IsSTS B₂) {f g h : Fin v} (hor : Oriented B₂ ψ f g h)
    (r s : Fin u) : #(crossTriple ψ L₁ L₂ f g h r s) = 3 := by
  obtain ⟨d1, d2, d3⟩ := hor.distinct h₂
  rw [crossTriple, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [d3]
  · simp [d1, d2]

theorem prod_isSTS (h₁ : IsSTS B₁) (h₂ : IsSTS B₂) (hψ : IsBicolouring B₂ ψ)
    (hL₁ : IsLatinSquare L₁) (hL₂ : IsLatinSquare L₂) : IsSTS (prodBlocks B₁ B₂ ψ L₁ L₂) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rcases mem_union.1 ht with ht | ht
    · obtain ⟨i, s, hs, rfl⟩ := mem_internal.1 ht
      rw [card_map, h₁.card_eq s hs]
    · obtain ⟨f, g, h, hor, r, s, rfl⟩ := mem_cross.1 ht
      exact card_crossTriple h₂ hor r s
  rintro ⟨i, p⟩ ⟨j, q⟩ hxy
  by_cases hij : i = j
  · subst hij
    have hpq : p ≠ q := fun h => hxy (by rw [h])
    obtain ⟨t, ⟨ht, hp, hq⟩, hu⟩ := h₁.pair p q hpq
    refine ⟨t.map (copyEmb i), ⟨mem_union_left _ (mem_internal.2 ⟨i, t, ht, rfl⟩),
      mem_copy.2 ⟨rfl, hp⟩, mem_copy.2 ⟨rfl, hq⟩⟩, ?_⟩
    rintro t' ⟨ht', hp', hq'⟩
    rcases mem_union.1 ht' with ht' | ht'
    · obtain ⟨i', s, hs, rfl⟩ := mem_internal.1 ht'
      obtain ⟨rfl, hp''⟩ := mem_copy.1 hp'
      rw [hu s ⟨hs, hp'', (mem_copy.1 hq').2⟩]
    · obtain ⟨f, g, h, hor, r, s, rfl⟩ := mem_cross.1 ht'
      obtain ⟨d1, d2, d3⟩ := hor.distinct h₂
      exfalso
      rcases crossTriple_first_mem hp' with rfl | rfl | rfl
      · exact hpq ((crossTriple_coord_f d1 d2 hp').trans (crossTriple_coord_f d1 d2 hq').symm)
      · exact hpq ((crossTriple_coord_g d1 d3 hp').trans (crossTriple_coord_g d1 d3 hq').symm)
      · exact hpq ((crossTriple_coord_h d2 d3 hp').trans (crossTriple_coord_h d2 d3 hq').symm)
  · obtain ⟨T, ⟨hT, hi, hj⟩, huT⟩ := h₂.pair i j hij
    obtain ⟨f, g, h, hor, hfgh⟩ := exists_oriented h₂ hψ hT
    obtain ⟨d1, d2, d3⟩ := hor.distinct h₂
    have hL := sel_isLatinSquare (ψ := ψ) hL₁ hL₂ f h
    have hmem : ∀ {k}, k ∈ T → k = f ∨ k = g ∨ k = h := fun {k} hk => by
      rw [← hfgh] at hk
      simpa using hk
    obtain ⟨r, s, hr, hs⟩ := crossTriple_exists (p := p) (q := q) hL hij (hmem hi) (hmem hj)
    refine ⟨crossTriple ψ L₁ L₂ f g h r s,
      ⟨mem_union_right _ (mem_cross.2 ⟨f, g, h, hor, r, s, rfl⟩), hr, hs⟩, ?_⟩
    rintro t' ⟨ht', hp', hq'⟩
    rcases mem_union.1 ht' with ht' | ht'
    · obtain ⟨i', s', -, rfl⟩ := mem_internal.1 ht'
      exact absurd ((mem_copy.1 hp').1.trans (mem_copy.1 hq').1.symm) hij
    · obtain ⟨f', g', h', hor', r', s', rfl⟩ := mem_cross.1 ht'
      have hT' : ({f', g', h'} : Finset (Fin v)) = T := by
        refine huT _ ⟨hor'.1, ?_, ?_⟩
        · rcases crossTriple_first_mem hp' with rfl | rfl | rfl <;> simp
        · rcases crossTriple_first_mem hq' with rfl | rfl | rfl <;> simp
      obtain ⟨rfl, rfl, rfl⟩ := hor.unique h₂ hor' (hfgh.trans hT'.symm)
      obtain ⟨rfl, rfl⟩ := crossTriple_unique hL d1 d2 d3 hij hr hs hp' hq'
      rfl

end STS

/-! ### The colouring is a bicolouring -/

theorem card_image_sub_const {s : Finset (Fin 3)} (k : Fin 3) :
    #(s.image fun x => x - k) = #s :=
  card_image_of_injective _ (sub_left_injective)

theorem prod_isBicolouring {B₁ : Finset (Finset (Fin u))} {B₂ : Finset (Finset (Fin v))}
    {φ : Fin u → Fin 3} {ψ : Fin v → Fin 3} {L₁ L₂ : Fin u → Fin u → Fin u}
    (hφ : IsBicolouring B₁ φ)
    (good₁ : ∀ r s, #({φ r, φ s, φ (L₁ r s) - 1} : Finset (Fin 3)) = 2)
    (good₂ : ∀ r s, #({φ r, φ s, φ (L₂ r s) - 2} : Finset (Fin 3)) = 2) :
    IsBicolouring (prodBlocks B₁ B₂ ψ L₁ L₂) (prodColour φ ψ) := by
  intro t ht
  rcases mem_union.1 ht with ht | ht
  · obtain ⟨i, s, hs, rfl⟩ := mem_internal.1 ht
    have : (s.map (copyEmb i)).image (prodColour φ ψ) = (s.image φ).image fun x => x - ψ i := by
      rw [map_eq_image, image_image, image_image]
      rfl
    rw [this, card_image_sub_const, hφ s hs]
  · obtain ⟨f, g, h, hor, r, s, rfl⟩ := mem_cross.1 ht
    obtain ⟨-, -, hψfg, hψh⟩ := hor
    set δ := ψ h - ψ f
    have himg : (crossTriple ψ L₁ L₂ f g h r s).image (prodColour φ ψ) =
        ({φ r, φ s, φ (sel ψ L₁ L₂ f h r s) - δ} : Finset (Fin 3)).image fun x => x - ψ f := by
      simp only [crossTriple, image_insert, image_singleton, prodColour]
      rw [← hψfg]
      simp only [δ, sub_sub, sub_add_cancel]
    rw [himg, card_image_sub_const]
    by_cases hδ : δ = 1
    · have hsel : sel ψ L₁ L₂ f h = L₁ := if_pos hδ
      rw [hsel, hδ]
      exact good₁ r s
    · have hsel : sel ψ L₁ L₂ f h = L₂ := if_neg hδ
      have hδ2 : δ = 2 := by
        have hδ0 : δ ≠ 0 := fun h0 => hψh (sub_eq_zero.1 h0)
        revert hδ hδ0
        generalize δ = e
        decide +revert
      rw [hsel, hδ2]
      exact good₂ r s

/-! ### Class sizes -/

theorem card_prodColour (φ : Fin u → Fin 3) (ψ : Fin v → Fin 3) (k : Fin 3) :
    #(colourClass (prodColour φ ψ) k) =
      #(colourClass ψ 0) * #(colourClass φ k) + #(colourClass ψ 1) * #(colourClass φ (k + 1)) +
        #(colourClass ψ 2) * #(colourClass φ (k + 2)) := by
  have h1 : #(colourClass (prodColour φ ψ) k) = ∑ i, #(colourClass φ (k + ψ i)) := by
    unfold colourClass
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.card_filter]
    refine sum_congr rfl fun p _ => ?_
    simp only [prodColour, sub_eq_iff_eq_add]
  have hj : ∀ j : Fin 3, ∑ i ∈ univ.filter (fun i => ψ i = j), #(colourClass φ (k + ψ i)) =
      #(colourClass ψ j) * #(colourClass φ (k + j)) := fun j =>
    sum_const_nat fun i hi => by rw [(mem_filter.1 hi).2]
  rw [h1, ← sum_fiberwise univ ψ (fun i => #(colourClass φ (k + ψ i))), Fin.sum_univ_three,
    hj, hj, hj, add_zero]

/-! ### Theorem 2.4 -/

/-- **Colbourn–Dinitz–Rosa, Theorem 2.4.** If there exists an `(a, b, c)`-bicolourable STS(`u`)
with `c = max(a, b, c)` and `c ≤ a + b`, and an `(x, y, z)`-bicolourable STS(`v`), then there
exists an `(ax + by + cz, ay + bz + cx, az + bx + cy)`-bicolourable STS(`uv`). -/
theorem bicolourable3_mul {u v a b c x y z : ℕ} (h₁ : Bicolourable3 u a b c)
    (hac : a ≤ c) (hbc : b ≤ c) (hcab : c ≤ a + b) (h₂ : Bicolourable3 v x y z) :
    Bicolourable3 (u * v) (a * x + b * y + c * z) (a * y + b * z + c * x)
      (a * z + b * x + c * y) := by
  obtain ⟨B₁, φ, hB₁, hφ, ha, hb, hc⟩ := h₁
  obtain ⟨B₂, ψ, hB₂, hψ, hx, hy, hz⟩ := h₂
  obtain ⟨L₁, L₂, hL₁, hL₂, good₁, good₂⟩ := exists_good_squares (φ := φ)
    (by rw [ha, hc]; exact hac) (by rw [hb, hc]; exact hbc) (by rw [ha, hb, hc]; exact hcab)
  apply Bicolourable3.swap₁₂
  have e : Fin v × Fin u ≃ Fin (u * v) := finProdFinEquiv.trans (finCongr (mul_comm v u))
  refine bicolourable3_of_equiv e (prod_isSTS hB₁ hB₂ hψ hL₁ hL₂)
    (prod_isBicolouring hφ good₁ good₂) ?_ ?_ ?_
  · rw [card_prodColour, hx, hy, hz]
    simp only [zero_add, show (0 : Fin 3) + 2 = 2 by rfl]
    rw [ha, hb, hc]
    ring
  · rw [card_prodColour, hx, hy, hz, show (1 : Fin 3) + 1 = 2 by rfl,
      show (1 : Fin 3) + 2 = 0 by rfl, hb, hc, ha]
    ring
  · rw [card_prodColour, hx, hy, hz, show (2 : Fin 3) + 1 = 0 by rfl,
      show (2 : Fin 3) + 2 = 1 by rfl, hc, ha, hb]
    ring

end CDR
