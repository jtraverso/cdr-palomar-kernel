/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Basic
public import CDRBicolour.Latin.Lemma23

/-!
# The Colbourn–Dinitz–Rosa product (EJC 6 (1999) #R25, Theorem 2.4)

Inner system `S` on `U` with colouring `cu`, every class of size at most `|U|/2` (`c ≤ a + b`);
outer system `T` on `W` with any strict bicolouring `cw` (classes may be empty, as in L162).
On `W × U` coloured by `(w, u) ↦ cu u - cw w`:

* a copy of `S` in every fibre `{w} × U`;
* for every block `{f, g, h}` of `T` with `cw f = cw g ≠ cw h`, the transversal triples
  `{(f, p), (g, q), (h, L p q)}`, where `L` is a forbidden Latin square for the offset
  `d = cw h - cw f` (`cu p + cu q + cu (L p q) ≠ d`, CDR Lemma 2.3).

A triple of `Fin 3` values has exactly two distinct entries iff its sum is nonzero; this is the
whole colour check.
-/

@[expose] public section

namespace CDRBicolour

open Finset CDRBicolour.Latin

theorem fin3_card_two : ∀ x y z : Fin 3, ({x, y, z} : Finset (Fin 3)).card = 2 ↔ x + y + z ≠ 0 := by
  decide

theorem fin3_orient : ∀ a b c : Fin 3, ({a, b, c} : Finset (Fin 3)).card = 2 →
    (a = b ∧ c ≠ a) ∨ (a = c ∧ b ≠ a) ∨ (b = c ∧ a ≠ b) := by decide

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- Orientation of a bicoloured block: two points of the same colour first. -/
theorem orient (cw : W → Fin 3) (B : Finset W) (h3 : B.card = 3) (h2 : (B.image cw).card = 2) :
    ∃ f g h, B = {f, g, h} ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h ∧ cw f = cw g ∧ cw h ≠ cw f := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 h3
  simp only [image_insert, image_singleton] at h2
  rcases fin3_orient _ _ _ h2 with ⟨e, n⟩ | ⟨e, n⟩ | ⟨e, n⟩
  · exact ⟨x, y, z, rfl, hxy, hxz, hyz, e, n⟩
  · refine ⟨x, z, y, ?_, hxz, hxy, Ne.symm hyz, e, n⟩
    ext v; simp only [mem_insert, mem_singleton]; tauto
  · refine ⟨y, z, x, ?_, hyz, Ne.symm hxy, Ne.symm hxz, e, n⟩
    ext v; simp only [mem_insert, mem_singleton]; tauto

/-- Latin squares avoiding a prescribed sum, from CDR Lemma 2.3. -/
theorem exists_latin_avoid (cu : U → Fin 3) (hbal : ∀ i, 2 * classSize cu i ≤ Fintype.card U)
    (d : Fin 3) (hd : d ≠ 0) : ∃ L : U → U → U, IsLatin L ∧ ∀ p q, cu p + cu q + cu (L p q) ≠ d := by
  classical
  have hd' : d = 1 ∨ d = 2 := by revert hd; revert d; decide
  rcases hd' with rfl | rfl
  · have hneg : ∀ i, 2 * csz (fun u => -cu u) i ≤ Fintype.card U := by
      intro i
      have : csz (fun u => -cu u) i = classSize cu (-i) := by
        simp only [csz, classSize]; congr 1; ext u
        simp only [mem_filter, mem_univ, true_and]
        have e : ∀ x i : Fin 3, -x = i ↔ x = -i := by decide
        exact e _ _
      rw [this]; exact hbal _
    obtain ⟨L, hL, hf⟩ := forbidden_latin _ hneg
    refine ⟨L, hL, fun p q h => hf p q ?_⟩
    have e : ∀ x y z : Fin 3, x + y + z = 1 → -x + -y + -z = 2 := by decide
    exact e _ _ _ h
  · obtain ⟨L, hL, hf⟩ := forbidden_latin cu (fun i => hbal i)
    exact ⟨L, hL, hf⟩

theorem latin_row_bij {L : U → U → U} (hL : IsLatin L) (p : U) : Function.Bijective (L p) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨fun q q' h => hL.1 p (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h, rfl⟩

theorem latin_col_bij {L : U → U → U} (hL : IsLatin L) (q : U) :
    Function.Bijective (fun p => L p q) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨fun p p' h => hL.2 q (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h, rfl⟩

/-- **CDR Theorem 2.4 (product).** -/
theorem cdr_product (S : STS U) (cu : U → Fin 3) (hS : IsStrictBicolouring S cu)
    (hbal : ∀ i, 2 * classSize cu i ≤ Fintype.card U)
    (T : STS W) (cw : W → Fin 3) (hT : IsStrictBicolouring T cw) :
    ∃ P : STS (W × U), IsStrictBicolouring P (fun z => cu z.2 - cw z.1) := by
  classical
  -- orientation of the outer blocks
  have hor : ∀ B : {B // B ∈ T.blocks}, ∃ o : W × W × W, B.1 = {o.1, o.2.1, o.2.2} ∧
      o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2 ∧ cw o.1 = cw o.2.1 ∧ cw o.2.2 ≠ cw o.1 := by
    intro B
    obtain ⟨f, g, h, e, h1, h2, h3, h4, h5⟩ := orient cw B.1 (T.card_eq_three _ B.2) (hT _ B.2)
    exact ⟨(f, g, h), e, h1, h2, h3, h4, h5⟩
  choose o ho using hor
  -- the Latin squares
  have hLat : ∀ B : {B // B ∈ T.blocks}, ∃ L : U → U → U, IsLatin L ∧
      ∀ p q, cu p + cu q + cu (L p q) ≠ cw (o B).2.2 - cw (o B).1 := by
    intro B
    refine exists_latin_avoid cu hbal _ ?_
    intro h; exact (ho B).2.2.2.2.2 (sub_eq_zero.1 h)
  choose L hL using hLat
  let fib : W → Finset U → Finset (W × U) := fun w B => B.image fun u => (w, u)
  let tri : {B // B ∈ T.blocks} → U → U → Finset (W × U) := fun B p q =>
    {((o B).1, p), ((o B).2.1, q), ((o B).2.2, L B p q)}
  have mem_fib : ∀ w B z, z ∈ fib w B ↔ z.1 = w ∧ z.2 ∈ B := by
    intro w B z
    simp only [fib, mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨rfl, hu⟩
    · rintro ⟨h1, h2⟩; exact ⟨z.2, h2, by rw [← h1]⟩
  have mem_tri : ∀ B p q z, z ∈ tri B p q ↔
      z = ((o B).1, p) ∨ z = ((o B).2.1, q) ∨ z = ((o B).2.2, L B p q) := by
    intro B p q z; simp [tri]
  -- reading a transversal triple
  have tri_read : ∀ B p q z, z ∈ tri B p q →
      (z.1 = (o B).1 → z.2 = p) ∧ (z.1 = (o B).2.1 → z.2 = q) ∧
        (z.1 = (o B).2.2 → z.2 = L B p q) ∧ z.1 ∈ B.1 := by
    intro B p q z hz
    obtain ⟨_, h1, h2, h3, -, -⟩ := ho B
    rw [(ho B).1]
    rcases (mem_tri B p q z).1 hz with rfl | rfl | rfl
    · exact ⟨fun _ => rfl, fun h => absurd h h1, fun h => absurd h h2, by simp⟩
    · exact ⟨fun h => absurd h.symm h1, fun _ => rfl, fun h => absurd h h3, by simp⟩
    · exact ⟨fun h => absurd h.symm h2, fun h => absurd h.symm h3, fun _ => rfl, by simp⟩
  have tri_W : ∀ B p q z z', z ∈ tri B p q → z' ∈ tri B p q → z.1 = z'.1 → z = z' := by
    intro B p q z z' hz hz' h
    obtain ⟨_, h1, h2, h3, -, -⟩ := ho B
    rcases (mem_tri B p q z).1 hz with rfl | rfl | rfl <;>
    rcases (mem_tri B p q z').1 hz' with rfl | rfl | rfl
    all_goals first
      | rfl
      | (exfalso; simp only at h
         first | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm
               | exact h3 h | exact h3 h.symm)
  let blocks : Finset (Finset (W × U)) :=
    ((univ : Finset W) ×ˢ S.blocks).image (fun wB => fib wB.1 wB.2) ∪
      (univ : Finset ({B // B ∈ T.blocks} × U × U)).image (fun x => tri x.1 x.2.1 x.2.2)
  have mem_blocks : ∀ Q, Q ∈ blocks ↔ (∃ w B, B ∈ S.blocks ∧ Q = fib w B) ∨
      (∃ B p q, Q = tri B p q) := by
    intro Q
    simp only [blocks, mem_union, mem_image, mem_product, mem_univ, true_and, Prod.exists]
    constructor
    · rintro (⟨w, B, hB, rfl⟩ | ⟨B, p, q, rfl⟩)
      · exact Or.inl ⟨w, B, hB, rfl⟩
      · exact Or.inr ⟨B, p, q, rfl⟩
    · rintro (⟨w, B, hB, rfl⟩ | ⟨B, p, q, rfl⟩)
      · exact Or.inl ⟨w, B, hB, rfl⟩
      · exact Or.inr ⟨B, p, q, rfl⟩
  refine ⟨⟨blocks, ?_, ?_⟩, ?_⟩
  · -- blocks have three points
    intro Q hQ
    rcases (mem_blocks Q).1 hQ with ⟨w, B, hB, rfl⟩ | ⟨B, p, q, rfl⟩
    · rw [card_image_of_injective _ (Prod.mk_right_injective w)]; exact S.card_eq_three B hB
    · obtain ⟨_, h1, h2, h3, -, -⟩ := ho B
      refine card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> intro h <;>
        simp only [Prod.mk.injEq] at h
      · exact h1 h.1
      · exact h2 h.1
      · exact h3 h.1
  · -- every pair in exactly one block
    rintro ⟨w₁, u₁⟩ ⟨w₂, u₂⟩ hxy
    by_cases hw : w₁ = w₂
    · subst hw
      have hu : u₁ ≠ u₂ := fun h => hxy (by rw [h])
      obtain ⟨B₀, ⟨hB₀, h1, h2⟩, huniq⟩ := S.existsUnique_block u₁ u₂ hu
      refine ⟨fib w₁ B₀, ⟨(mem_blocks _).2 (Or.inl ⟨w₁, B₀, hB₀, rfl⟩),
        (mem_fib _ _ _).2 ⟨rfl, h1⟩, (mem_fib _ _ _).2 ⟨rfl, h2⟩⟩, ?_⟩
      rintro Q ⟨hQ, hxQ, hyQ⟩
      rcases (mem_blocks Q).1 hQ with ⟨w, B, hB, rfl⟩ | ⟨B, p, q, rfl⟩
      · rw [mem_fib] at hxQ hyQ
        simp only at hxQ hyQ
        rw [← hxQ.1, huniq B ⟨hB, hxQ.2, hyQ.2⟩]
      · exact absurd (tri_W B p q _ _ hxQ hyQ rfl) hxy
    · obtain ⟨B₀, ⟨hB₀, h1, h2⟩, huniq⟩ := T.existsUnique_block w₁ w₂ hw
      set Bs : {B // B ∈ T.blocks} := ⟨B₀, hB₀⟩
      obtain ⟨hBo, hfg, hfh, hgh, -, -⟩ := ho Bs
      have h1' : w₁ ∈ ({(o Bs).1, (o Bs).2.1, (o Bs).2.2} : Finset W) := by
        rw [← hBo]; exact h1
      have h2' : w₂ ∈ ({(o Bs).1, (o Bs).2.1, (o Bs).2.2} : Finset W) := by
        rw [← hBo]; exact h2
      simp only [mem_insert, mem_singleton] at h1' h2'
      have hrow := latin_row_bij (hL Bs).1
      have hcol := latin_col_bij (hL Bs).1
      -- existence of a transversal triple through both points
      have hex : ∃ p q, (w₁, u₁) ∈ tri Bs p q ∧ (w₂, u₂) ∈ tri Bs p q := by
        rcases h1' with e1 | e1 | e1 <;> rcases h2' with e2 | e2 | e2
        · exact absurd (e1.trans e2.symm) hw
        · exact ⟨u₁, u₂, (mem_tri _ _ _ _).2 (Or.inl (by rw [e1])),
            (mem_tri _ _ _ _).2 (Or.inr (Or.inl (by rw [e2])))⟩
        · obtain ⟨q, hq⟩ := (hrow u₁).2 u₂
          exact ⟨u₁, q, (mem_tri _ _ _ _).2 (Or.inl (by rw [e1])),
            (mem_tri _ _ _ _).2 (Or.inr (Or.inr (by rw [e2, hq])))⟩
        · exact ⟨u₂, u₁, (mem_tri _ _ _ _).2 (Or.inr (Or.inl (by rw [e1]))),
            (mem_tri _ _ _ _).2 (Or.inl (by rw [e2]))⟩
        · exact absurd (e1.trans e2.symm) hw
        · obtain ⟨p, hp⟩ := (hcol u₁).2 u₂
          exact ⟨p, u₁, (mem_tri _ _ _ _).2 (Or.inr (Or.inl (by rw [e1]))),
            (mem_tri _ _ _ _).2 (Or.inr (Or.inr (by rw [e2]; simp only at hp; rw [hp])))⟩
        · obtain ⟨q, hq⟩ := (hrow u₂).2 u₁
          exact ⟨u₂, q, (mem_tri _ _ _ _).2 (Or.inr (Or.inr (by rw [e1, hq]))),
            (mem_tri _ _ _ _).2 (Or.inl (by rw [e2]))⟩
        · obtain ⟨p, hp⟩ := (hcol u₂).2 u₁
          exact ⟨p, u₂, (mem_tri _ _ _ _).2 (Or.inr (Or.inr (by rw [e1]; simp only at hp; rw [hp]))),
            (mem_tri _ _ _ _).2 (Or.inr (Or.inl (by rw [e2])))⟩
        · exact absurd (e1.trans e2.symm) hw
      obtain ⟨p, q, hxp, hyp⟩ := hex
      refine ⟨tri Bs p q, ⟨(mem_blocks _).2 (Or.inr ⟨Bs, p, q, rfl⟩), hxp, hyp⟩, ?_⟩
      rintro Q ⟨hQ, hxQ, hyQ⟩
      rcases (mem_blocks Q).1 hQ with ⟨w, B, hB, rfl⟩ | ⟨B, p', q', rfl⟩
      · rw [mem_fib] at hxQ hyQ
        exact absurd (hxQ.1.trans hyQ.1.symm) hw
      · -- the outer block is `B₀`
        have hB : B = Bs := Subtype.ext (huniq B.1 ⟨B.2, (tri_read B p' q' _ hxQ).2.2.2,
          (tri_read B p' q' _ hyQ).2.2.2⟩)
        subst hB
        -- read `p'`, `q'` from the two points
        obtain ⟨ax, bx, cx, -⟩ := tri_read _ p' q' _ hxQ
        obtain ⟨ay, bY, cy, -⟩ := tri_read _ p' q' _ hyQ
        obtain ⟨ax', bx', cx', -⟩ := tri_read _ p q _ hxp
        obtain ⟨ay', bY', cy', -⟩ := tri_read _ p q _ hyp
        simp only at ax bx cx ay bY cy ax' bx' cx' ay' bY' cy'
        have hpq : p' = p ∧ q' = q := by
          rcases h1' with e1 | e1 | e1 <;> rcases h2' with e2 | e2 | e2
          · exact absurd (e1.trans e2.symm) hw
          · exact ⟨(ax e1).symm.trans (ax' e1), (bY e2).symm.trans (bY' e2)⟩
          · have hp : p' = p := (ax e1).symm.trans (ax' e1)
            subst hp
            exact ⟨rfl, (hrow p').1 ((cy e2).symm.trans (cy' e2))⟩
          · exact ⟨(ay e2).symm.trans (ay' e2), (bx e1).symm.trans (bx' e1)⟩
          · exact absurd (e1.trans e2.symm) hw
          · have hq : q' = q := (bx e1).symm.trans (bx' e1)
            subst hq
            exact ⟨(hcol q').1 ((cy e2).symm.trans (cy' e2)), rfl⟩
          · have hp : p' = p := (ay e2).symm.trans (ay' e2)
            subst hp
            exact ⟨rfl, (hrow p').1 ((cx e1).symm.trans (cx' e1))⟩
          · have hq : q' = q := (bY e2).symm.trans (bY' e2)
            subst hq
            exact ⟨(hcol q').1 ((cx e1).symm.trans (cx' e1)), rfl⟩
          · exact absurd (e1.trans e2.symm) hw
        rw [hpq.1, hpq.2]
  · -- every block sees exactly two colours
    intro Q hQ
    rcases (mem_blocks Q).1 hQ with ⟨w, B, hB, rfl⟩ | ⟨B, p, q, rfl⟩
    · have : (fib w B).image (fun z => cu z.2 - cw z.1) = (B.image cu).image (· - cw w) := by
        simp only [fib, image_image]; rfl
      rw [this, card_image_of_injective _ (sub_left_injective)]
      exact hS B hB
    · obtain ⟨-, -, -, -, hfg, -⟩ := ho B
      simp only [tri, image_insert, image_singleton]
      rw [fin3_card_two, ← hfg]
      have e : ∀ x y z k k' : Fin 3, x + y + z ≠ k' - k → (x - k) + (y - k) + (z - k') ≠ 0 := by
        decide
      exact e _ _ _ _ _ ((hL B).2 p q)

end CDRBicolour
