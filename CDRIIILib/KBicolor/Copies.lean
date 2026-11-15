/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Exact.Copies
public import CDRIIILib.KBicolor.Monitored
public import CDRIIILib.KBicolor.BRIk

/-!
# Copies of the bicoloured trade for `k` classes

A placement (`Place`) gives, for each index `j` (a triple of classes `τ j : Fin 3 → Fin k`,
injective), an injective family of points `ψ (j, i, x)` (`i : Fin 9`, `x : ℤ_m`) with
`ψ (j, i, x)` in class `τ j (i / 3)`, jointly injective in `(j, i, x)`. The copy
`c = (j, s, t)` puts model point `i` at `ψ (j, i, s + i t)`.

* `copy_edgeG`: two copies sharing an edge coincide (`m` prime, `m > 8`);
* `packG σ` (half `T₁` in the copies with `σ c`, `T₀` elsewhere) is a packing of bicoloured
  triangles (`packG_allowed`, `packG_disj`) whose leave does not depend on `σ` (`packG_leave`)
  and has degree `≤ 9 m` (`degL_leaveG`);
* `packG_count`: the type counts are a constant plus `Σ_c [σ c] (m₁ − m₀)`;
* `model_YZ`: for the roles `(0, 1, 2)` the trade moves type `112` by `−1` and type `221` by `+1`;
* `exists_place`: a placement exists when every class has at least `9 |J| m` points.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact

/-- A placement of the copies. -/
structure Place {V : Type*} {k : ℕ} (lab : V → Fin k) (J : Type*) (m : ℕ) where
  τ : J → Fin 3 → Fin k
  τinj : ∀ j, Function.Injective (τ j)
  ψ : J × Fin 9 × ZMod m → V
  ψinj : Function.Injective ψ
  ψlab : ∀ j i x, lab (ψ (j, i, x)) = τ j (mcol i)

variable {V : Type*} [DecidableEq V] {k m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
  {lab : V → Fin k} (P : Place lab J m)

/-- Model point `i` of copy `c = (j, s, t)`. -/
def phiG (c : J × ZMod m × ZMod m) (i : Fin 9) : V :=
  P.ψ (c.1, i, c.2.1 + (i.val : ZMod m) * c.2.2)

theorem phiG_inj (c : J × ZMod m × ZMod m) : Function.Injective (phiG P c) := fun i i' h =>
  congrArg (fun p : J × Fin 9 × ZMod m => p.2.1) (P.ψinj h)

/-- The embedding of a copy. -/
def phiGE (c : J × ZMod m × ZMod m) : Fin 9 ↪ V := ⟨phiG P c, phiG_inj P c⟩

theorem lab_phiG (c : J × ZMod m × ZMod m) (i : Fin 9) : lab (phiG P c i) = P.τ c.1 (mcol i) :=
  P.ψlab _ _ _

/-- **Two copies sharing an edge coincide.** -/
theorem copy_edgeG [Fact m.Prime] (hm : 8 < m) {c c' : J × ZMod m × ZMod m}
    {a b a' b' : Fin 9} (hab : a ≠ b)
    (he : s(phiG P c a, phiG P c b) = s(phiG P c' a', phiG P c' b')) : c = c' := by
  have key : ∀ {a b a' b' : Fin 9}, a ≠ b → phiG P c a = phiG P c' a' →
      phiG P c b = phiG P c' b' → c = c' := by
    intro a b a' b' hab h1 h2
    have e1 := P.ψinj h1
    have e2 := P.ψinj h2
    simp only [Prod.mk.injEq] at e1 e2
    obtain ⟨hj, rfl, x1⟩ := e1
    obtain ⟨-, rfl, x2⟩ := e2
    have ht : ((a.val : ZMod m) - (b.val : ZMod m)) * (c.2.2 - c'.2.2) = 0 := by
      linear_combination x1 - x2
    rcases mul_eq_zero.mp ht with h0 | h0
    · exact absurd h0 (natCast_ne hm hab)
    · have ht' : c.2.2 = c'.2.2 := sub_eq_zero.mp h0
      have hs : c.2.1 = c'.2.1 := by rw [ht'] at x1; linear_combination x1
      exact Prod.ext hj (Prod.ext hs ht')
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key hab h1 h2
  · exact key hab h1 h2

/-- The half chosen by `σ`. -/
def halfOfG (σ : J × ZMod m × ZMod m → Bool) (c : J × ZMod m × ZMod m) : Finset (Finset V) :=
  if σ c then half1 (phiGE P c) else half0 (phiGE P c)

variable [NeZero m]

/-- The packing. -/
def packG (σ : J × ZMod m × ZMod m → Bool) : Finset (Finset V) := univ.biUnion (halfOfG P σ)

/-- The common leave. -/
def leaveG : Finset (Sym2 V) := univ.biUnion fun c => (half1 (phiGE P c)).biUnion triEdges

theorem mem_halfOfG {σ : J × ZMod m × ZMod m → Bool} {c : J × ZMod m × ZMod m} {T : Finset V}
    (hT : T ∈ halfOfG P σ c) :
    ∃ T₀ : Finset (Fin 9), (T₀ ∈ T1m ∨ T₀ ∈ T0m) ∧ T = T₀.map (phiGE P c) := by
  unfold halfOfG half1 half0 at hT
  split_ifs at hT
  · obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT; exact ⟨T₀, Or.inl h₀, rfl⟩
  · obtain ⟨T₀, h₀, rfl⟩ := mem_image.mp hT; exact ⟨T₀, Or.inr h₀, rfl⟩

theorem edge_of_mapG {c : J × ZMod m × ZMod m} {T₀ : Finset (Fin 9)} {e : Sym2 V}
    (he : e ∈ triEdges (T₀.map (phiGE P c))) :
    ∃ a b : Fin 9, a ≠ b ∧ a ∈ T₀ ∧ b ∈ T₀ ∧ e = s(phiG P c a, phiG P c b) := by
  rw [triEdges_map, mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  induction e' using Sym2.ind with
  | _ a b =>
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he'
  exact ⟨a, b, he'.2, he'.1.1, he'.1.2, rfl⟩

theorem map_lab_model (c : J × ZMod m × ZMod m) (T₀ : Finset (Fin 9)) :
    (T₀.map (phiGE P c)).val.map lab = (T₀.val.map mcol).map (P.τ c.1) := by
  rw [map_val, Multiset.map_map, Multiset.map_map]
  congr 1
  funext i
  exact lab_phiG P c i

theorem packG_allowed [Fintype V] (σ : J × ZMod m × ZMod m → Bool) :
    ∀ T ∈ packG P σ, IsAllowed (kHost lab) (bicF k) T := by
  intro T hT
  obtain ⟨c, -, hc⟩ := mem_biUnion.mp hT
  obtain ⟨T₀, h₀, rfl⟩ := mem_halfOfG P hc
  have hc3 : T₀.card = 3 := by
    rcases h₀ with h₀ | h₀
    · exact model_card.1 T₀ h₀
    · exact model_card.2 T₀ h₀
  have hbi : (T₀.image mcol).card = 2 := by
    rcases h₀ with h₀ | h₀
    · exact model_bicol.1 T₀ h₀
    · exact model_bicol.2 T₀ h₀
  refine ⟨by rw [card_map]; exact hc3, fun x _ y _ hxy => by simpa [kHost] using hxy, ?_⟩
  show (T₀.map (phiGE P c)).val.map lab ∈ bicF k
  rw [map_lab_model, map_mem_bicF (P.τinj c.1)]
  refine ⟨by simp [hc3], ?_⟩
  rw [Multiset.toFinset_map, Finset.val_toFinset]
  exact hbi

theorem packG_disj [Fact m.Prime] (hm : 8 < m) (σ : J × ZMod m × ZMod m → Bool) :
    ((packG P σ : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint triEdges := by
  intro T hT T' hT' hne
  simp only [mem_coe, packG, mem_biUnion, mem_univ, true_and] at hT hT'
  obtain ⟨c, hc⟩ := hT
  obtain ⟨c', hc'⟩ := hT'
  by_cases hcc : c = c'
  · subst hcc
    unfold halfOfG at hc hc'
    split_ifs at hc hc'
    · exact half1_disj (phiGE P c) hc hc' hne
    · exact half0_disj (phiGE P c) hc hc' hne
  · show Disjoint (triEdges T) (triEdges T')
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨T₀, -, rfl⟩ := mem_halfOfG P hc
    obtain ⟨T₀', -, rfl⟩ := mem_halfOfG P hc'
    obtain ⟨a, b, hab, -, -, rfl⟩ := edge_of_mapG P he
    obtain ⟨a', b', -, -, -, he2⟩ := edge_of_mapG P he'
    exact hcc (copy_edgeG P hm hab he2)

theorem packG_leave (σ : J × ZMod m × ZMod m → Bool) :
    (packG P σ).biUnion triEdges = leaveG P := by
  unfold packG leaveG
  rw [biUnion_biUnion]
  refine biUnion_congr rfl fun c _ => ?_
  unfold halfOfG
  split_ifs
  · rfl
  · exact (union_eq (phiGE P c)).symm

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- Degree of the leave. -/
theorem degL_leaveG [Fintype V] (v : V) : degL (leaveG P) v ≤ 9 * m := by
  by_cases hv : ∃ p, P.ψ p = v
  · obtain ⟨⟨j, i, x⟩, rfl⟩ := hv
    have hsub : nbL (leaveG P) (P.ψ (j, i, x)) ⊆
        (univ : Finset (ZMod m × Fin 9)).image
          fun p => P.ψ (j, p.2, x - (i.val : ZMod m) * p.1 + (p.2.val : ZMod m) * p.1) := by
      intro w hw
      simp only [nbL, mem_filter, mem_univ, true_and] at hw
      rw [leaveG, mem_biUnion] at hw
      obtain ⟨c, -, hc⟩ := hw
      rw [mem_biUnion] at hc
      obtain ⟨T, hT, he⟩ := hc
      obtain ⟨T₀, -, rfl⟩ := mem_image.mp hT
      obtain ⟨a, b, -, -, -, he2⟩ := edge_of_mapG P he
      rw [Sym2.eq_iff] at he2
      have main : ∀ a b : Fin 9, w = phiG P c a → P.ψ (j, i, x) = phiG P c b →
          w ∈ (univ : Finset (ZMod m × Fin 9)).image
            fun p => P.ψ (j, p.2, x - (i.val : ZMod m) * p.1 + (p.2.val : ZMod m) * p.1) := by
        intro a b hw hvb
        have e := P.ψinj hvb
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, hx⟩ := e
        refine mem_image.mpr ⟨(c.2.2, a), mem_univ _, ?_⟩
        rw [hw]
        simp only [phiG]
        congr 3
        rw [hx]; ring
      rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact main a b h1 h2
      · exact main b a h1 h2
    calc degL (leaveG P) (P.ψ (j, i, x)) ≤ #((univ : Finset (ZMod m × Fin 9)).image
          fun p => P.ψ (j, p.2, x - (i.val : ZMod m) * p.1 + (p.2.val : ZMod m) * p.1)) :=
          card_le_card hsub
      _ ≤ #(univ : Finset (ZMod m × Fin 9)) := card_image_le
      _ = 9 * m := by simp [Fintype.card_prod, ZMod.card]; ring
  · push Not at hv
    have : nbL (leaveG P) v = ∅ := by
      ext w
      simp only [nbL, mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      intro hw
      rw [leaveG, mem_biUnion] at hw
      obtain ⟨c, -, hc⟩ := hw
      rw [mem_biUnion] at hc
      obtain ⟨T, hT, he⟩ := hc
      obtain ⟨T₀, -, rfl⟩ := mem_image.mp hT
      obtain ⟨a, b, -, -, -, he2⟩ := edge_of_mapG P he
      rw [Sym2.eq_iff] at he2
      rcases he2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> exact hv _ h2.symm
    simp [degL, this]

/-! ### Type counts -/

/-- Number of model triangles of a half whose placed labels form `{X, X, Y}`. -/
def mcnt (τ : Fin 3 → Fin k) (S : Finset (Finset (Fin 9))) (X Y : Fin k) : ℕ :=
  #(S.filter fun T => (T.val.map mcol).map τ = {X, X, Y})

theorem half_count (c : J × ZMod m × ZMod m) (S : Finset (Finset (Fin 9))) (X Y : Fin k) :
    kTypeCount lab (S.image fun T => T.map (phiGE P c)) X Y = mcnt (P.τ c.1) S X Y := by
  unfold kTypeCount mcnt
  rw [filter_image, card_image_of_injective _ (map_inj (phiGE P c))]
  congr 1
  refine filter_congr fun T _ => ?_
  rw [map_lab_model]

theorem halves_pairwiseG [Fact m.Prime] (hm : 8 < m) (σ : J × ZMod m × ZMod m → Bool) :
    ((univ : Finset (J × ZMod m × ZMod m)) : Set (J × ZMod m × ZMod m)).PairwiseDisjoint
      (halfOfG P σ) := by
  intro c _ c' _ hcc
  rw [Function.onFun, Finset.disjoint_left]
  intro T hT hT'
  obtain ⟨T₀, h₀, rfl⟩ := mem_halfOfG P hT
  obtain ⟨T₀', -, he⟩ := mem_halfOfG P hT'
  have hc3 : T₀.card = 3 := by
    rcases h₀ with h₀ | h₀
    · exact model_card.1 T₀ h₀
    · exact model_card.2 T₀ h₀
  obtain ⟨x, y, z, hxy, -, -, rfl⟩ := card_eq_three.mp hc3
  have hmem : s(phiGE P c x, phiGE P c y) ∈
      triEdges (({x, y, z} : Finset (Fin 9)).map (phiGE P c)) := by
    rw [triEdges_map, mem_map]
    exact ⟨s(x, y), by simp [triEdges, hxy], rfl⟩
  rw [he] at hmem
  obtain ⟨a', b', -, -, -, he2⟩ := edge_of_mapG P hmem
  exact hcc (copy_edgeG P hm hxy he2)

/-- **Type counts of the packing.** -/
theorem packG_count [Fact m.Prime] (hm : 8 < m) (σ : J × ZMod m × ZMod m → Bool) (X Y : Fin k) :
    (kTypeCount lab (packG P σ) X Y : ℤ) =
      ∑ c : J × ZMod m × ZMod m, (mcnt (P.τ c.1) T0m X Y : ℤ) +
        ∑ c : J × ZMod m × ZMod m, (if σ c then
          ((mcnt (P.τ c.1) T1m X Y : ℤ) - mcnt (P.τ c.1) T0m X Y) else 0) := by
  have h : kTypeCount lab (packG P σ) X Y =
      ∑ c : J × ZMod m × ZMod m, kTypeCount lab (halfOfG P σ c) X Y := by
    unfold kTypeCount packG
    rw [filter_biUnion, card_biUnion]
    intro c hc c' hc' hcc
    exact disjoint_filter_filter (halves_pairwiseG P hm σ (mem_coe.2 hc) (mem_coe.2 hc') hcc)
  rw [h]
  push_cast
  rw [← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  unfold halfOfG half1 half0
  split_ifs
  · rw [half_count]; ring
  · rw [half_count]; ring

/-! ### The trade on the cycle coordinates -/

theorem mcnt_map {τ : Fin 3 → Fin k} (hτ : Function.Injective τ) (S : Finset (Finset (Fin 9)))
    (a b : Fin 3) :
    mcnt τ S (τ a) (τ b) = #(S.filter fun T => T.val.map mcol = {a, a, b}) := by
  unfold mcnt
  congr 1
  refine filter_congr fun T _ => ?_
  rw [show ({τ a, τ a, τ b} : Multiset (Fin k)) = ({a, a, b} : Multiset (Fin 3)).map τ by simp]
  exact (Multiset.map_injective hτ).eq_iff

set_option maxRecDepth 100000 in
/-- The trade on the types `112` and `221` of the model. -/
theorem model_YZ :
    (T1m.filter fun T => T.val.map mcol = ({1, 1, 2} : Multiset (Fin 3))).card = 1 ∧
    (T0m.filter fun T => T.val.map mcol = ({1, 1, 2} : Multiset (Fin 3))).card = 2 ∧
    (T1m.filter fun T => T.val.map mcol = ({2, 2, 1} : Multiset (Fin 3))).card = 2 ∧
    (T0m.filter fun T => T.val.map mcol = ({2, 2, 1} : Multiset (Fin 3))).card = 1 := by
  decide +kernel

/-! ### Existence of a placement -/

omit [DecidableEq J] in
/-- **A placement exists** when every class has at least `9 |J| m` points. -/
theorem exists_place [Fintype V] (lab : V → Fin k) (τ : J → Fin 3 → Fin k)
    (hτ : ∀ j, Function.Injective (τ j))
    (hm : ∀ X, 9 * Fintype.card J * m ≤ ksz lab X) : ∃ P : Place lab J m, P.τ = τ := by
  classical
  let A : Fin k → Type _ := fun X => {p : J × Fin 9 // τ p.1 (mcol p.2) = X}
  let B : Fin k → Type _ := fun X => {v : V // lab v = X}
  have hcard : ∀ X, Fintype.card (A X × ZMod m) ≤ Fintype.card (B X) := by
    intro X
    have h1 : Fintype.card (A X) ≤ Fintype.card (J × Fin 9) := Fintype.card_subtype_le _
    have h2 : Fintype.card (B X) = ksz lab X := by
      simp only [B, ksz]; exact Fintype.card_subtype _
    rw [Fintype.card_prod, ZMod.card, h2]
    rw [Fintype.card_prod, Fintype.card_fin] at h1
    calc Fintype.card (A X) * m ≤ Fintype.card J * 9 * m := Nat.mul_le_mul_right _ h1
      _ = 9 * Fintype.card J * m := by ring
      _ ≤ ksz lab X := hm X
  let e : ∀ X, A X × ZMod m ↪ B X := fun X =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (hcard X))
  -- the glued injection on the sigma type
  let F : (Σ X, A X × ZMod m) → V := fun s => (e s.1 s.2).1
  have hF : Function.Injective F := by
    rintro ⟨X, a⟩ ⟨X', a'⟩ h
    have hX : X = X' := by
      have l1 : lab (e X a).1 = X := (e X a).2
      have l2 : lab (e X' a').1 = X' := (e X' a').2
      have h' : (e X a).1 = (e X' a').1 := h
      rw [← l1, ← l2, h']
    subst hX
    have : e X a = e X a' := Subtype.ext h
    rw [(e X).injective this]
  let cs : J × Fin 9 × ZMod m → Σ X, A X × ZMod m := fun p =>
    ⟨τ p.1 (mcol p.2.1), (⟨(p.1, p.2.1), rfl⟩, p.2.2)⟩
  have hcs : Function.Injective cs := by
    intro p p' h
    have : (fun s : Σ X, A X × ZMod m => (s.2.1.1.1, s.2.1.1.2, s.2.2)) (cs p) =
        (fun s : Σ X, A X × ZMod m => (s.2.1.1.1, s.2.1.1.2, s.2.2)) (cs p') := by rw [h]
    exact this
  exact ⟨Place.mk τ hτ (F ∘ cs) (hF.comp hcs)
    (fun j i x => (e (τ j (mcol i)) (⟨(j, i), rfl⟩, x)).2), rfl⟩

end CDRBicolour.KBicolor
