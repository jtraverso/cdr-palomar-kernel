/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Label67

/-!
# The staircase labelling of `H*`: properties

`stairOf`: the labelling of `insert v* HV` as a `StairData`, with `q = |HV|` (`stairOf_q`), the
matching edges joining a left end to the right end of the same index (`adj_of_idx_eq`,
`idx_eq_of_adj`), and the orientation facts used for the pairing of `X` with `Y`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rankIn_lt_of_key {S : Finset V} {key : V → ℕ} {a b : V} (ha : a ∈ S)
    (hab : key a < key b) : rankIn S key a < rankIn S key b := by
  unfold rankIn
  apply card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · rw [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hab⟩
  · have := hsub (mem_filter.2 ⟨ha, hab⟩)
    simp at this

variable {M : SimpleGraph V} {X Y HV : Finset V} {vs : V}
  (hM : IsMatchingGraph M) (hMS : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV)

include hMS in
theorem partner_mem {v : V} (hv : v ∈ cover M) : partner M v ∈ HV :=
  (hMS v _ (adj_partner hv)).2

theorem mem_leftM {v : V} : v ∈ leftM M X Y HV ↔ v ∈ HV ∧ v ∈ cover M ∧ Pref X Y v (partner M v) := by
  unfold leftM; rw [mem_filter]

theorem mem_unm {v : V} : v ∈ unm M HV ↔ v ∈ HV ∧ v ∉ cover M := by
  unfold unm; rw [mem_filter]

include hM hMS in
theorem partner_mem_leftM {v : V} (hv : v ∈ HV) (hc : v ∈ cover M) (hL : v ∉ leftM M X Y HV) :
    partner M v ∈ leftM M X Y HV := by
  rw [mem_leftM] at hL ⊢
  refine ⟨partner_mem hMS hc, partner_mem_cover hc, ?_⟩
  rw [partner_partner hM hc]
  rcases pref_or (X := X) (Y := Y) (partner_ne hc) with h | h
  · exact h
  · exact absurd ⟨hv, hc, h⟩ hL

include hM in
theorem partner_not_leftM {v : V} (hv : v ∈ leftM M X Y HV) : partner M v ∉ leftM M X Y HV := by
  intro h
  have hc := (mem_leftM.1 hv).2.1
  have h1 := (mem_leftM.1 hv).2.2
  have h2 := (mem_leftM.1 h).2.2
  rw [partner_partner hM hc] at h2
  exact pref_asymm h1 h2

include hM hMS in
theorem card_HV : #HV = 2 * #(leftM M X Y HV) + #(unm M HV) := by
  set Lm := leftM M X Y HV
  set Rm := HV.filter fun v => v ∈ cover M ∧ v ∉ Lm
  have h1 : #HV = #(HV.filter fun v => v ∈ cover M) + #(unm M HV) := by
    rw [← card_filter_add_card_filter_not (s := HV) (p := fun v => v ∈ cover M)]
    rfl
  have h2 : #(HV.filter fun v => v ∈ cover M) = #Lm + #Rm := by
    rw [← card_filter_add_card_filter_not (s := HV.filter fun v => v ∈ cover M) (p := (· ∈ Lm))]
    congr 1
    · congr 1; ext v
      simp only [mem_filter, Lm, mem_leftM]
      tauto
    · congr 1; ext v
      simp only [mem_filter, Rm]
      tauto
  have h3 : #Rm = #Lm := by
    have himg : Lm.image (partner M) = Rm := by
      ext v
      simp only [mem_image, Rm, mem_filter]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hc := (mem_leftM.1 hu).2.1
        exact ⟨partner_mem hMS hc, partner_mem_cover hc, partner_not_leftM hM hu⟩
      · rintro ⟨hv, hc, hL⟩
        exact ⟨partner M v, partner_mem_leftM hM hMS hv hc hL, partner_partner hM hc⟩
    rw [← himg, card_image_of_injOn]
    intro a ha b hb e
    have hca := (mem_leftM.1 ha).2.1
    have hcb := (mem_leftM.1 hb).2.1
    rw [← partner_partner hM hca, ← partner_partner hM hcb]
    exact congrArg (partner M) e
  omega

omit hM hMS in
/-- The staircase labelling of `insert v* HV`. -/
noncomputable def stairOf (hM' : IsMatchingGraph M) (hMS' : ∀ a b, M.Adj a b → a ∈ HV ∧ b ∈ HV)
    (hvs' : vs ∉ HV) : StairData (insert vs HV) where
  side := sideOf M X Y HV vs
  idx := idxOf M X Y HV vs
  t := 1 - #(unm M HV)
  m := #(leftM M X Y HV)
  ht := by omega
  hm := by omega
  hL := by
    intro v hv hs
    simp only [sideOf, decide_eq_true_eq] at hs
    unfold idxOf
    rcases hs with rfl | hs
    · simp
    · have hvne : v ≠ vs := fun e => hvs' (e ▸ (mem_leftM.1 hs).1)
      rw [if_neg hvne, if_pos hs]
      have := rankIn_lt (key := code) hs
      omega
  hR := by
    intro v hv hs
    simp only [sideOf, decide_eq_false_iff_not, not_or] at hs
    obtain ⟨hvne, hL⟩ := hs
    have hvH : v ∈ HV := (mem_insert.1 hv).resolve_left hvne
    unfold idxOf
    rw [if_neg hvne, if_neg hL]
    split_ifs with hc
    · have := rankIn_lt (key := code) (partner_mem_leftM hM' hMS' hvH hc hL)
      omega
    · have := rankIn_lt (key := ukey X Y) (mem_unm.2 ⟨hvH, hc⟩)
      omega
  injL := by
    intro u hu v hv hsu hsv e
    simp only [sideOf, decide_eq_true_eq] at hsu hsv
    unfold idxOf at e
    rcases hsu with rfl | hsu <;> rcases hsv with rfl | hsv
    · rfl
    · have hne : v ≠ u := fun h => hvs' (h ▸ (mem_leftM.1 hsv).1)
      rw [if_pos rfl, if_neg hne, if_pos hsv] at e
      have := rankIn_lt (key := code) hsv
      omega
    · have hne : u ≠ v := fun h => hvs' (h ▸ (mem_leftM.1 hsu).1)
      rw [if_pos rfl, if_neg hne, if_pos hsu] at e
      have := rankIn_lt (key := code) hsu
      omega
    · have hune : u ≠ vs := fun h => hvs' (h ▸ (mem_leftM.1 hsu).1)
      have hvne : v ≠ vs := fun h => hvs' (h ▸ (mem_leftM.1 hsv).1)
      rw [if_neg hune, if_pos hsu, if_neg hvne, if_pos hsv] at e
      exact rankIn_injOn (key := code) (fun a _ b _ h => code_inj h) hsu hsv (by omega)
  injR := by
    intro u hu v hv hsu hsv e
    simp only [sideOf, decide_eq_false_iff_not, not_or] at hsu hsv
    obtain ⟨hune, hLu⟩ := hsu
    obtain ⟨hvne, hLv⟩ := hsv
    have huH : u ∈ HV := (mem_insert.1 hu).resolve_left hune
    have hvH : v ∈ HV := (mem_insert.1 hv).resolve_left hvne
    unfold idxOf at e
    rw [if_neg hune, if_neg hLu, if_neg hvne, if_neg hLv] at e
    by_cases hcu : u ∈ cover M <;> by_cases hcv : v ∈ cover M <;>
      simp only [hcu, hcv, if_true, if_false] at e
    · have := rankIn_injOn (key := code) (fun a _ b _ h => code_inj h) (partner_mem_leftM hM' hMS' huH hcu hLu)
        (partner_mem_leftM hM' hMS' hvH hcv hLv) (by omega)
      rw [← partner_partner hM' hcu, ← partner_partner hM' hcv, this]
    · have := rankIn_lt (key := ukey X Y) (mem_unm.2 ⟨hvH, hcv⟩)
      omega
    · have := rankIn_lt (key := ukey X Y) (mem_unm.2 ⟨huH, hcu⟩)
      omega
    · exact rankIn_injOn (key := ukey X Y) (fun a _ b _ h => ukey_inj h) (mem_unm.2 ⟨huH, hcu⟩)
        (mem_unm.2 ⟨hvH, hcv⟩) (by omega)

variable {hM hMS} {hvs : vs ∉ HV}

theorem stairOf_side : (stairOf (X := X) (Y := Y) (hM' := hM) (hMS' := hMS) (hvs' := hvs)).side = sideOf M X Y HV vs := rfl
theorem stairOf_idx : (stairOf (X := X) (Y := Y) (hM' := hM) (hMS' := hMS) (hvs' := hvs)).idx = idxOf M X Y HV vs := rfl
theorem stairOf_m : (stairOf (X := X) (Y := Y) (hM' := hM) (hMS' := hMS) (hvs' := hvs)).m = #(leftM M X Y HV) := rfl

theorem stairOf_q : (stairOf (X := X) (Y := Y) (hM' := hM) (hMS' := hMS) (hvs' := hvs)).q = #HV := by
  unfold StairData.q
  have := card_HV (X := X) (Y := Y) hM hMS
  simp only [stairOf]
  omega

theorem side_vs : sideOf M X Y HV vs vs = true := by simp [sideOf]

theorem idx_vs : idxOf M X Y HV vs vs = #(leftM M X Y HV) + 1 := by simp [idxOf]

theorem side_of_mem {v : V} (hv : v ∈ HV) (hvs : vs ∉ HV) :
    sideOf M X Y HV vs v = true ↔ v ∈ leftM M X Y HV := by
  have : v ≠ vs := fun e => hvs (e ▸ hv)
  simp [sideOf, this]

include hM hMS in
/-- A matching edge joins a left end to the right end of the same index. -/
theorem idx_eq_of_adj (hvs : vs ∉ HV) {l r : V} (hl : l ∈ leftM M X Y HV) (hlr : M.Adj l r) :
    sideOf M X Y HV vs r = false ∧ idxOf M X Y HV vs r = idxOf M X Y HV vs l := by
  have hlH := (mem_leftM.1 hl).1
  have hrH := (hMS l r hlr).2
  have hcl : l ∈ cover M := mem_cover.2 ⟨r, hlr⟩
  have hcr : r ∈ cover M := mem_cover.2 ⟨l, hlr.symm⟩
  have hpr : partner M r = l := partner_eq hM hlr.symm
  have hpl : partner M l = r := partner_eq hM hlr
  have hrL : r ∉ leftM M X Y HV := hpl ▸ partner_not_leftM hM hl
  have hlne : l ≠ vs := fun e => hvs (e ▸ hlH)
  have hrne : r ≠ vs := fun e => hvs (e ▸ hrH)
  refine ⟨by simp [sideOf, hrne, hrL], ?_⟩
  unfold idxOf
  rw [if_neg hrne, if_neg hrL, if_pos hcr, hpr, if_neg hlne, if_pos hl]

include hM hMS in
/-- Conversely, a left end and a right end with the same index are matched. -/
theorem adj_of_idx_eq (hvs : vs ∉ HV) {l r : V} (hl : l ∈ leftM M X Y HV) (hrH : r ∈ HV)
    (hrL : r ∉ leftM M X Y HV) (he : idxOf M X Y HV vs l = idxOf M X Y HV vs r) : M.Adj l r := by
  have hlH := (mem_leftM.1 hl).1
  have hlne : l ≠ vs := fun e => hvs (e ▸ hlH)
  have hrne : r ≠ vs := fun e => hvs (e ▸ hrH)
  unfold idxOf at he
  rw [if_neg hlne, if_pos hl, if_neg hrne, if_neg hrL] at he
  split_ifs at he with hcr
  · have := rankIn_injOn (key := code) (fun a _ b _ h => code_inj h) hl (partner_mem_leftM hM hMS hrH hcr hrL)
      (by omega)
    rw [this]
    exact (adj_partner hcr).symm
  · have := rankIn_lt (key := ukey X Y) (mem_unm.2 ⟨hrH, hcr⟩)
    omega

theorem idx_unm_le (hvs : vs ∉ HV) {v : V} (hv : v ∈ unm M HV) : idxOf M X Y HV vs v ≤ 0 := by
  obtain ⟨hvH, hc⟩ := mem_unm.1 hv
  have hne : v ≠ vs := fun e => hvs (e ▸ hvH)
  have hL : v ∉ leftM M X Y HV := fun h => hc (mem_leftM.1 h).2.1
  unfold idxOf
  rw [if_neg hne, if_neg hL, if_neg hc]
  have := rankIn_lt (key := ukey X Y) hv
  omega

theorem idx_matched_pos (hvs : vs ∉ HV) {v : V} (hv : v ∈ HV) (hc : v ∈ cover M) :
    1 ≤ idxOf M X Y HV vs v := by
  have hne : v ≠ vs := fun e => hvs (e ▸ hv)
  unfold idxOf
  rw [if_neg hne]
  split_ifs <;> omega

/-- Unmatched `Y`-vertices come before unmatched `X`-vertices. -/
theorem idx_unm_lt (hvs : vs ∉ HV) (hXY : Disjoint X Y) {y x : V} (hy : y ∈ unm M HV) (hyY : y ∈ Y)
    (hx : x ∈ unm M HV) (hxX : x ∈ X) : idxOf M X Y HV vs y < idxOf M X Y HV vs x := by
  have hxY : x ∉ Y := fun h => disjoint_left.1 hXY hxX h
  have hk : ukey X Y y < ukey X Y x := by
    unfold ukey
    rw [if_pos hyY, if_neg hxY, if_pos hxX]
    have := code_lt y
    omega
  have hlt := rankIn_lt_of_key hy hk
  obtain ⟨hyH, hyc⟩ := mem_unm.1 hy
  obtain ⟨hxH, hxc⟩ := mem_unm.1 hx
  have hyne : y ≠ vs := fun e => hvs (e ▸ hyH)
  have hxne : x ≠ vs := fun e => hvs (e ▸ hxH)
  have hyL : y ∉ leftM M X Y HV := fun h => hyc (mem_leftM.1 h).2.1
  have hxL : x ∉ leftM M X Y HV := fun h => hxc (mem_leftM.1 h).2.1
  unfold idxOf
  rw [if_neg hyne, if_neg hyL, if_neg hyc, if_neg hxne, if_neg hxL, if_neg hxc]
  omega

include hM in
/-- A left end in `X` is matched to a right end in `X`. -/
theorem X_left {x : V} (hxX : x ∈ X) (hx : x ∈ leftM M X Y HV) :
    partner M x ∈ X ∧ partner M x ∉ leftM M X Y HV := by
  refine ⟨?_, partner_not_leftM hM hx⟩
  have h := (mem_leftM.1 hx).2.2
  by_contra hp
  unfold Pref prio at h
  by_cases hpY : partner M x ∈ Y <;> simp [hxX, hp, hpY] at h

include hM hMS in
/-- A matched right end in `Y` is matched to a left end in `Y`. -/
theorem Y_right (hXY : Disjoint X Y) {y : V} (hyY : y ∈ Y) (hyH : y ∈ HV) (hc : y ∈ cover M)
    (hy : y ∉ leftM M X Y HV) : partner M y ∈ Y ∧ partner M y ∈ leftM M X Y HV := by
  have hpL := partner_mem_leftM hM hMS hyH hc hy
  refine ⟨?_, hpL⟩
  have h := (mem_leftM.1 hpL).2.2
  rw [partner_partner hM hc] at h
  have hyX : y ∉ X := fun h => disjoint_left.1 hXY h hyY
  by_contra hp
  unfold Pref prio at h
  by_cases hpX : partner M y ∈ X <;> simp [hyX, hyY, hp, hpX] at h

end OneFactor
