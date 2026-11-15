/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.MainPaperIIITriangleMonitors
public import CDRIIILib.KBicolor.Main

/-!
# Type counts of k-bicolourings: the approximate spectrum (monitored Theorem T)

For a labelling `lab` with classes `c_X` and seed data `a` (`SeedData`), the seed of `kH1` puts
mass `c_X c_Y a_XY / 2` on the triangles of type `XXY` (`seed_mass`, from `card_xxy`:
there are `C(c_X, 2) c_Y` of them). Theorem T with triangle monitors
(`main_theorem_T_with_triangle_monitors`, Paper III) then gives:

`kbicolour_monitored`: every large admissible labelling with seed data `a ≥ η` is the class
partition of a k-bicoloured STS whose number of blocks of type `XXY` is
`c_X c_Y a_XY / 2 ± ε n²`, simultaneously for all ordered pairs `X ≠ Y`.

Since `a_XY = 2 t_XY / (c_X c_Y)` turns any type-count target `t` satisfying the linear
identities `t_XY + t_YX = c_X c_Y / 2`, `Σ_Y t_XY = C(c_X, 2)` into seed data, this is the
approximate type spectrum in the interior.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle

variable {k : ℕ}

/-- Number of blocks of type `XXY` (two points of class `X`, one of class `Y`). -/
def kTypeCount {V : Type*} (lab : V → Fin k) (D : Finset (Finset V)) (X Y : Fin k) : ℕ :=
  #(D.filter fun T => T.val.map lab = {X, X, Y})

/-! ### Counting triangles of a given type -/

theorem count_lab {V : Type*} [DecidableEq V] (lab : V → Fin k) (T : Finset V) (Z : Fin k) :
    (T.val.map lab).count Z = #(T.filter fun v => lab v = Z) := by
  rw [Multiset.count_map, card_def, filter_val]
  congr 1
  exact Multiset.filter_congr fun x _ => eq_comm

theorem map_triple_lab {V : Type*} [DecidableEq V] (f : V → Fin k) {p q r : V} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    ({p, q, r} : Finset V).val.map f = {f p, f q, f r} := by
  rw [insert_val_of_notMem (by simp [hpq, hpr]), insert_val_of_notMem (by simp [hqr])]
  simp

theorem xxy_mem_bicF {X Y : Fin k} (hXY : X ≠ Y) : ({X, X, Y} : Multiset (Fin k)) ∈ bicF k :=
  mem_bicF.2 (Or.inl ⟨rfl, hXY⟩)

/-- There are `C(c_X, 2) c_Y` triangles of type `XXY`. -/
theorem card_xxy {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k) {X Y : Fin k}
    (hXY : X ≠ Y) :
    #(univ.filter fun T : Finset V => T.card = 3 ∧ T.val.map lab = {X, X, Y}) =
      (ksz lab X).choose 2 * ksz lab Y := by
  set A := univ.filter fun v : V => lab v = X with hA
  set B := univ.filter fun v : V => lab v = Y with hB
  have hcX : ({X, X, Y} : Multiset (Fin k)).count X = 2 := by simp [hXY]
  have hcY : ({X, X, Y} : Multiset (Fin k)).count Y = 1 := by simp [Ne.symm hXY]
  have hinj : Set.InjOn (fun p : Finset V × V => insert p.2 p.1) (A.powersetCard 2 ×ˢ B : Finset _) := by
    rintro ⟨P, z⟩ hp ⟨P', z'⟩ hp' heq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powersetCard, hA, hB, mem_filter,
      mem_univ, true_and] at hp hp'
    simp only at heq
    have hzP : z ∉ P := fun h => hXY ((mem_filter.1 (hp.1.1 h)).2.symm.trans hp.2)
    have hzP' : z' ∉ P' := fun h => hXY ((mem_filter.1 (hp'.1.1 h)).2.symm.trans hp'.2)
    have hz : z = z' := by
      have hz' : z' ∈ insert z P := heq ▸ mem_insert_self z' P'
      rcases mem_insert.1 hz' with h | h
      · exact h.symm
      · exact absurd ((mem_filter.1 (hp.1.1 h)).2.symm.trans hp'.2) hXY
    subst hz
    refine Prod.ext ?_ rfl
    simp only
    rw [← erase_insert hzP, ← erase_insert hzP', heq]
  have key : (univ.filter fun T : Finset V => T.card = 3 ∧ T.val.map lab = {X, X, Y}) =
      (A.powersetCard 2 ×ˢ B).image (fun p => insert p.2 p.1) := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_product, mem_powersetCard,
      Prod.exists]
    constructor
    · rintro ⟨hT3, hm⟩
      have h2 : #(T.filter fun v => lab v = X) = 2 := by rw [← count_lab, hm, hcX]
      have h1 : #(T.filter fun v => lab v = Y) = 1 := by rw [← count_lab, hm, hcY]
      obtain ⟨y, hy⟩ := card_eq_one.1 h1
      have hyT : y ∈ T ∧ lab y = Y := mem_filter.1 (hy ▸ mem_singleton_self y)
      refine ⟨T.filter fun v => lab v = X, y, ⟨⟨fun v hv => ?_, h2⟩, ?_⟩, ?_⟩
      · exact mem_filter.2 ⟨mem_univ v, (mem_filter.1 hv).2⟩
      · exact mem_filter.2 ⟨mem_univ y, hyT.2⟩
      · ext v
        simp only [mem_insert, mem_filter]
        constructor
        · rintro (rfl | ⟨hv, -⟩)
          · exact hyT.1
          · exact hv
        · intro hv
          by_cases hvX : lab v = X
          · exact Or.inr ⟨hv, hvX⟩
          · left
            by_cases hvY : lab v = Y
            · have : v ∈ T.filter (fun w => lab w = Y) := mem_filter.2 ⟨hv, hvY⟩
              rw [hy] at this
              exact mem_singleton.1 this
            · exfalso
              have h0 : #(T.filter fun w => lab w = lab v) = 0 := by
                rw [← count_lab, hm]
                simpa using ⟨hvX, hvY⟩
              rw [card_eq_zero] at h0
              have : v ∈ T.filter (fun w => lab w = lab v) := mem_filter.2 ⟨hv, rfl⟩
              rw [h0] at this
              exact absurd this (notMem_empty v)
    · rintro ⟨P, y, ⟨⟨hPA, hP2⟩, hyB⟩, rfl⟩
      have hyY : lab y = Y := (mem_filter.1 hyB).2
      obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hP2
      have hpX : lab p = X := (mem_filter.1 (hPA (by simp))).2
      have hqX : lab q = X := (mem_filter.1 (hPA (by simp))).2
      have hyp : y ≠ p := fun h => hXY (hpX.symm.trans (h ▸ hyY))
      have hyq : y ≠ q := fun h => hXY (hqX.symm.trans (h ▸ hyY))
      refine ⟨?_, ?_⟩
      · rw [card_insert_of_notMem (by simp [hyp, hyq]), card_pair hpq]
      · rw [show (insert y {p, q} : Finset V) = {y, p, q} from rfl,
          map_triple_lab lab hyp hyq hpq, hyY, hpX, hqX, perm_abb]
  rw [key, card_image_of_injOn hinj, card_product, card_powersetCard]
  rfl

/-- The seed of `kH1` puts mass `c_X c_Y a_XY / 2` on the type `XXY`. -/
theorem seed_mass {V : Type*} [Fintype V] [DecidableEq V] (lab : V → Fin k)
    (a : Fin k → Fin k → ℝ) {X Y : Fin k} (hXY : X ≠ Y) (hc : 2 ≤ ksz lab X) :
    ∑ Q ∈ allowed (kHost lab) (bicF k),
        seedW (ksz lab) a (Q.val.map lab) * (if Q.val.map lab = {X, X, Y} then 1 else 0) =
      (ksz lab X : ℝ) * ksz lab Y * a X Y / 2 := by
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have hval : ∀ Q ∈ (allowed (kHost lab) (bicF k)).filter (fun Q => Q.val.map lab = {X, X, Y}),
      seedW (ksz lab) a (Q.val.map lab) = a X Y / ((ksz lab X : ℝ) - 1) := fun Q hQ => by
    rw [(mem_filter.1 hQ).2, seedW_xxy _ _ hXY]
  rw [sum_congr rfl hval, sum_const, nsmul_eq_mul]
  have hfilt : (allowed (kHost lab) (bicF k)).filter (fun Q => Q.val.map lab = {X, X, Y}) =
      univ.filter (fun T : Finset V => T.card = 3 ∧ T.val.map lab = {X, X, Y}) := by
    ext T
    simp only [allowed, IsAllowed, mem_filter, mem_univ, true_and, kHost, SimpleGraph.top_adj]
    constructor
    · rintro ⟨⟨h3, -, -⟩, hm⟩; exact ⟨h3, hm⟩
    · rintro ⟨h3, hm⟩; exact ⟨⟨h3, fun x _ y _ hxy => hxy, hm ▸ xxy_mem_bicF hXY⟩, hm⟩
  rw [hfilt, card_xxy lab hXY]
  push_cast
  rw [Nat.cast_choose_two]
  have hc1 : (ksz lab X : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ ksz lab X := by exact_mod_cast hc
    linarith
  field_simp

/-- **Monitored k-bicolourings.** Type counts follow the seed up to `ε n²`. -/
theorem kbicolour_monitored (k : ℕ) (hk : 2 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ a, SeedData (ksz lab) η a →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
        ∀ X Y, X ≠ Y →
          |(kTypeCount lab D X Y : ℝ) - (ksz lab X : ℝ) * ksz lab Y * a X Y / 2| ≤
            ε * (n : ℝ) ^ 2 := by
  have hC : (1 : ℝ) ≤ 1 / η + 2 / δ := by
    have : 2 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 0 < 1 / η := by positivity
    linarith
  obtain ⟨N, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors (bicF k) (δ ^ 2 / 4)
    (1 / η + 2 / δ) ε 6 2 (by positivity) hC le_rfl hε
  refine ⟨max N (max (Nat.ceil (10 / δ)) k), fun n lab hn hodd hcls heven hdiv a ha => ?_⟩
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have h10 : 10 ≤ δ * (Fintype.card (Fin n) : ℝ) := by
    rw [hcard]
    have : (Nat.ceil (10 / δ) : ℝ) ≤ n := by
      exact_mod_cast (le_max_left _ _).trans (le_of_max_le_right hn)
    have := (div_le_iff₀ hδ).1 ((Nat.le_ceil _).trans this)
    linarith
  have hkn : k ≤ n := (le_max_right _ _).trans (le_of_max_le_right hn)
  have hcls' : ∀ X, δ * (Fintype.card (Fin n) : ℝ) ≤ ksz lab X := by
    intro X; rw [hcard]; exact hcls X
  -- H1
  have H1 := kH1 lab hη hδ ha hcls' (by linarith)
  -- H3
  have H3 := commonNbr_mono (kH3 lab hcls' (by linarith))
    (by nlinarith : δ ^ 2 / 4 ≤ δ / 2)
  -- H4
  have H4 := kH4 lab hδ hcls' h10
  -- H2
  have hbig : Big lab := by
    intro X u v
    set S := univ.filter fun w : Fin n => lab w = X with hS
    have h3 : 3 ≤ S.card := by
      have : (3 : ℝ) ≤ S.card := by have := hcls' X; unfold ksz at this; linarith
      exact_mod_cast this
    have h1 := pred_card_le_card_erase (s := S.erase u) (a := v)
    have h2 := pred_card_le_card_erase (s := S) (a := u)
    obtain ⟨w, hw⟩ : ((S.erase u).erase v).Nonempty := by
      rw [← card_pos]; omega
    simp only [mem_erase, hS, mem_filter, mem_univ, true_and] at hw
    exact ⟨w, hw.2.2, hw.2.1, hw.1⟩
  have hnpos : 0 < n := by obtain ⟨m, hm⟩ := hodd; omega
  have hex : ∀ X : Fin k, ∃ v, lab v = X := fun X => by
    obtain ⟨w, hw, -⟩ := hbig X ⟨0, hnpos⟩ ⟨0, hnpos⟩
    · exact ⟨w, hw⟩
  choose o ho using hex
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X h
    simp only [nx] at h
    split_ifs at h with h0
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn' : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have H2 := physical_of (lab := lab) hbig ho hnx ⟨0, by omega⟩ hn' heven
    (pair_of_div (ksz lab) hsum hdiv)
  -- monitors: one per ordered pair of classes
  let w : Fin k × Fin k → Finset (Fin n) → ℝ := fun j Q =>
    if Q.val.map lab = {j.1, j.1, j.2} then 1 else 0
  have hν : (Fintype.card (Fin k × Fin k) : ℝ) ≤ (Fintype.card (Fin n) : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, hcard]
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hw : ∀ j Q, IsAllowed (kHost lab) (bicF k) Q → |w j Q| ≤ 1 := fun j Q _ => by
    simp only [w]; split_ifs <;> norm_num
  obtain ⟨D, hD, hstat⟩ := hT (kHost lab) (fun T => seedW (ksz lab) a (T.val.map lab))
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) H1 H2 H3 H4 (Fin k × Fin k) w hν hw
  refine ⟨D, hD, fun X Y hXY => ?_⟩
  have h := hstat (X, Y)
  have e1 : ∑ Q ∈ D, w (X, Y) Q = (kTypeCount lab D X Y : ℝ) := by
    simp only [w, kTypeCount]; rw [sum_boole]
  have hc2 : 2 ≤ ksz lab X := by
    have : (2 : ℝ) ≤ ksz lab X := by have := hcls' X; linarith
    exact_mod_cast this
  have e2 : ∑ Q ∈ allowed (kHost lab) (bicF k),
      (fun T : Finset (Fin n) => seedW (ksz lab) a (T.val.map lab)) Q * w (X, Y) Q =
        (ksz lab X : ℝ) * ksz lab Y * a X Y / 2 := seed_mass lab a hXY hc2
  rw [e1, e2, hcard] at h
  exact h

/-- Seed data from an integer type-count target in the interior. -/
theorem seedData_of_target {V : Type*} [Fintype V] (lab : V → Fin k) {η : ℝ}
    (t : Fin k → Fin k → ℕ) (hpos : ∀ X, 0 < ksz lab X)
    (hpair : ∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y)
    (hrow : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1))
    (hlow : ∀ X Y, X ≠ Y → η * ksz lab X * ksz lab Y ≤ 2 * t X Y) :
    SeedData (ksz lab) η (fun X Y => 2 * t X Y / ((ksz lab X : ℝ) * ksz lab Y)) := by
  have hc : ∀ X, (0 : ℝ) < ksz lab X := fun X => by exact_mod_cast hpos X
  refine ⟨fun X Y hXY => ?_, fun X Y hXY => ?_, fun X => ?_⟩
  · have h := hpair X Y hXY
    have h' : (2 : ℝ) * (t X Y + t Y X) = ksz lab X * ksz lab Y := by exact_mod_cast h
    have hXY0 := (mul_pos (hc X) (hc Y)).ne'
    have hYX0 := (mul_pos (hc Y) (hc X)).ne'
    rw [div_add_div _ _ hXY0 hYX0, div_eq_one_iff_eq (mul_ne_zero hXY0 hYX0)]
    have e : (ksz lab Y : ℝ) * ksz lab X = ksz lab X * ksz lab Y := mul_comm _ _
    rw [e]; nlinarith [h']
  · rw [le_div_iff₀ (mul_pos (hc X) (hc Y))]
    have := hlow X Y hXY
    have h2 : ((2 * t X Y : ℕ) : ℝ) = 2 * (t X Y : ℝ) := by push_cast; ring
    linarith [show η * ↑(ksz lab X) * ↑(ksz lab Y) ≤ ((2 * t X Y : ℕ) : ℝ) by exact_mod_cast this]
  · have hr := hrow X
    have hr' : (2 : ℝ) * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), (t X Y : ℝ) =
        (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1) := by
      have h1 : 1 ≤ ksz lab X := hpos X
      have : ((2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y : ℕ) : ℝ) =
          ((ksz lab X * (ksz lab X - 1) : ℕ) : ℝ) := by rw [hr]
      push_cast [Nat.cast_sub h1] at this
      exact this
    have e : ∀ Y ∈ univ.filter (fun Y => Y ≠ X),
        (ksz lab Y : ℝ) * (2 * t X Y / ((ksz lab X : ℝ) * ksz lab Y)) =
          2 * (t X Y : ℝ) / ksz lab X := fun Y _ => by
      field_simp [(hc X).ne', (hc Y).ne']
    rw [sum_congr rfl e, ← sum_div, ← mul_sum, hr']
    field_simp [(hc X).ne']

/-- **Approximate type spectrum (interior).** Every integer type-count target satisfying the
linear identities, with all entries at least `η c_X c_Y / 2`, is realised up to `ε n²`. -/
theorem kbicolour_types_approx (k : ℕ) (hk : 2 ≤ k) {δ η ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1)) →
      (∀ X Y, X ≠ Y → η * ksz lab X * ksz lab Y ≤ 2 * t X Y) →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
        ∀ X Y, X ≠ Y → |(kTypeCount lab D X Y : ℝ) - t X Y| ≤ ε * (n : ℝ) ^ 2 := by
  obtain ⟨n₀, h⟩ := kbicolour_monitored k hk hδ hδ1 hη hε
  refine ⟨max n₀ 1, fun n lab hn hodd hcls heven hdiv t hpair hrow hlow => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpos : ∀ X, 0 < ksz lab X := fun X => by
    have : (0 : ℝ) < ksz lab X := lt_of_lt_of_le (by positivity) (hcls X)
    exact_mod_cast this
  obtain ⟨D, hD, hcnt⟩ := h n lab (le_of_max_le_left hn) hodd hcls heven hdiv _
    (seedData_of_target lab t hpos hpair hrow hlow)
  refine ⟨D, hD, fun X Y hXY => ?_⟩
  have hc : ∀ X, (0 : ℝ) < ksz lab X := fun X => by exact_mod_cast hpos X
  have e : (ksz lab X : ℝ) * ksz lab Y * (2 * t X Y / ((ksz lab X : ℝ) * ksz lab Y)) / 2 =
      t X Y := by
    field_simp [(hc X).ne', (hc Y).ne']
  have := hcnt X Y hXY
  rwa [e] at this

end CDRBicolour.KBicolor
