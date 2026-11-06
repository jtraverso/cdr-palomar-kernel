/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.Exposure
public import RequestProject.S10K.SourceRecursion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23 / S05 §§2–3 with `B = E(T)`: the finite random process of ONE source triangle

For a source `T = {u, v, a}` (its own probability space; nothing is shared with other
sources) the process makes exactly 12 queries (S05 (7) with `k = 3`):

| query | choice | option set |
|---|---|---|
| 0, 1, 2 | pivot apices `b1, b2, b3` for `uv, ua, va` | permitted thirds, minus the third vertex of `T` |
| 3 | bridge `c` for `uv` | permitted thirds outside the history |
| 4, 5 | hinges `J1` (`u,v,a,c`), `J2` (`u,v,c,b1`) | original hinges of the order fixed by the roots, fresh |
| 6, 7, 8 | bridge `c1`, hinges `J3` (`u,a,x1,c1`), `J4` (`u,a,c1,b2`) | idem, or a dummy if `Q1` is the pivot |
| 9, 10, 11 | bridge `c2`, hinges `J5` (`v,a,x2,c2`), `J6` (`v,a,c2,b3`) | idem, or a dummy if `Q2` is the pivot |

Each query is uniform on its option set (`Expo.wt`). The hinge order `ordH` is fixed from
the roots (least admissible order given by H4) BEFORE the edge set is chosen; a hinge option
is an EDGE SET (original object), "fresh" = its support meets the history only in its four
roots. Every option set is GUARDED by its size: an apex set is used only if it has
`≥ αn/2` elements and a hinge set only if it has `≥ (α/2) n^(i-4)` elements (otherwise a
dummy with no new vertex is used). With this guard the per-query ratio S05 (8) holds for
EVERY history (`opts_step`), so the first-arrival bound applies (`exposure_src`).

That the guards are satisfied at all positive-probability histories (so that the dummies
never occur except in the skip case) is proved in `SourceReach.lean` from H3/H4.
-/

open Finset

noncomputable section
open Classical

namespace S10V23.Proc

open TypedTriangle.SparseEdge S10V22 S10V23

variable {V I : Type*} [Fintype V]

/-- Answers of a query: an apex (vertex) or an edge set (hinge, or the dummy `∅`). -/
abbrev Opt (V : Type*) := V ⊕ Finset (Sym2 V)

/-- Vertices revealed by an answer. -/
def vsO : Opt V → Finset V := Sum.elim (fun y => {y}) support

/-- The dummy answer (reveals nothing). -/
def dflt : Opt V := Sum.inr ∅

/-- Decoders. -/
def gv (d : V) : Opt V → V := Sum.elim id (fun _ => d)
def gJ : Opt V → Finset (Sym2 V) := Sum.elim (fun _ => ∅) id

/-- Replace an empty option set by the dummy. -/
def nz (s : Finset (Opt V)) : Finset (Opt V) := if s.Nonempty then s else {dflt}

omit [Fintype V] in
lemma nz_nonempty (s : Finset (Opt V)) : (nz s).Nonempty := by
  unfold nz; split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty _

lemma vsO_dflt : vsO (dflt : Opt V) = ∅ := by simp [vsO, dflt, support]

variable (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (al : ℝ) (hh : ℕ)

/-- Permitted thirds of `pq` outside `excl`. -/
def apexSet (p q : V) (excl : Finset V) : Finset V :=
  univ.filter (fun y => IsAllowed G lab F {p, q, y} ∧ y ∉ excl)

/-- Guarded apex query. -/
def apexStep (p q : V) (excl : Finset V) : Finset (Opt V) :=
  if al * (Fintype.card V : ℝ) / 2 ≤ (apexSet G lab F p q excl).card then
    (apexSet G lab F p q excl).image Sum.inl else ∅

/-- The hinge order fixed by the roots (least order supplied by H4, or `0`). -/
def ordH (p q x y : V) : ℕ :=
  if hc : ∃ i, 6 ≤ i ∧ i ≤ hh ∧
      al * (Fintype.card V : ℝ) ^ (i - 4) ≤ (hinges G lab F p q x y i).card then
    Nat.find hc else 0

/-- Fresh original hinges (edge sets) of the fixed order. -/
def freshSet (p q x y : V) (Hs : Finset V) : Finset (Finset (Sym2 V)) :=
  (hinges G lab F p q x y (ordH G lab F al hh p q x y)).filter
    (fun J => Disjoint (support J) (Hs \ {p, q, x, y}))

/-- Guard of a hinge query. -/
def hingeOK (p q x y : V) (Hs : Finset V) : Prop :=
  p ≠ q ∧ p ≠ x ∧ q ≠ x ∧ p ≠ y ∧ q ≠ y ∧ x ≠ y ∧ ({p, q, x, y} : Finset V) ⊆ Hs ∧
    4 ≤ ordH G lab F al hh p q x y ∧ ordH G lab F al hh p q x y ≤ hh ∧
    al / 2 * (Fintype.card V : ℝ) ^ (ordH G lab F al hh p q x y - 4) ≤
      (freshSet G lab F al hh p q x y Hs).card

/-- Guarded hinge query. -/
def hingeStep (p q x y : V) (Hs : Finset V) : Finset (Opt V) :=
  if hingeOK G lab F al hh p q x y Hs then (freshSet G lab F al hh p q x y Hs).image Sum.inr
  else ∅

variable (u v a : V)

/-- Option set of query `k`, reading the previous answers `g j` (`j < k`). -/
def stepOpts (k : ℕ) (g : ℕ → Opt V) (Hs : Finset V) : Finset (Opt V) :=
  match k with
  | 0 => apexStep G lab F al u v {a}
  | 1 => apexStep G lab F al u a {v}
  | 2 => apexStep G lab F al v a {u}
  | 3 => apexStep G lab F al u v Hs
  | 4 => hingeStep G lab F al hh u v a (gv u (g 3)) Hs
  | 5 => hingeStep G lab F al hh u v (gv u (g 3)) (gv u (g 0)) Hs
  | 6 => if x1 G lab F u v a (gJ (g 4)) = gv u (g 1) then {dflt}
      else apexStep G lab F al u a Hs
  | 7 => if x1 G lab F u v a (gJ (g 4)) = gv u (g 1) then {dflt}
      else hingeStep G lab F al hh u a (x1 G lab F u v a (gJ (g 4))) (gv u (g 6)) Hs
  | 8 => if x1 G lab F u v a (gJ (g 4)) = gv u (g 1) then {dflt}
      else hingeStep G lab F al hh u a (gv u (g 6)) (gv u (g 1)) Hs
  | 9 => if x2 G lab F u v a (gJ (g 4)) = gv u (g 2) then {dflt}
      else apexStep G lab F al v a Hs
  | 10 => if x2 G lab F u v a (gJ (g 4)) = gv u (g 2) then {dflt}
      else hingeStep G lab F al hh v a (x2 G lab F u v a (gJ (g 4))) (gv u (g 9)) Hs
  | 11 => if x2 G lab F u v a (gJ (g 4)) = gv u (g 2) then {dflt}
      else hingeStep G lab F al hh v a (gv u (g 9)) (gv u (g 2)) Hs
  | _ => {dflt}

/-- Exposed vertices after a history: `T` and everything revealed. -/
def HS (h : List (Opt V)) : Finset V := {u, v, a} ∪ h.toFinset.biUnion vsO

/-- The option set after a history. -/
def opts (h : List (Opt V)) : Finset (Opt V) :=
  nz (stepOpts G lab F al hh u v a h.length (fun j => h.getD j dflt) (HS u v a h))

lemma opts_nonempty (h : List (Opt V)) : (opts G lab F al hh u v a h).Nonempty :=
  nz_nonempty _

lemma HS_append (h : List (Opt V)) (o : Opt V) :
    HS u v a (h ++ [o]) ⊆ HS u v a h ∪ vsO o := by
  intro x hx
  simp only [HS, List.toFinset_append, Finset.mem_union, Finset.mem_biUnion,
    List.mem_toFinset, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    Finset.mem_singleton] at hx ⊢
  rcases hx with hx | ⟨o', ho', hx⟩
  · exact Or.inl (Or.inl hx)
  · rcases ho' with ho' | rfl
    · exact Or.inl (Or.inr ⟨o', ho', hx⟩)
    · exact Or.inr hx

lemma HS_nil : HS u v a ([] : List (Opt V)) = {u, v, a} := by simp [HS]

/-! ## The per-query ratio holds for every history -/

/-- The ratio property of an option set. -/
def Good (q : ℝ) (Hs : Finset V) (O : Finset (Opt V)) : Prop :=
  ∀ W : Finset V, W.Nonempty → Disjoint W Hs →
    ((O.filter (fun o => W ⊆ vsO o)).card : ℝ) ≤ q ^ W.card * O.card

variable {G lab F al hh u v a}

lemma good_empty {q : ℝ} {Hs : Finset V} : Good q Hs (∅ : Finset (Opt V)) := by
  intro W _ _; simp

lemma good_dflt {q : ℝ} (hq : 0 ≤ q) {Hs : Finset V} : Good q Hs ({dflt} : Finset (Opt V)) := by
  intro W hW _
  have : ({dflt} : Finset (Opt V)).filter (fun o => W ⊆ vsO o) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun o ho => ?_
    rw [Finset.mem_singleton.1 ho, vsO_dflt]
    exact fun h => hW.ne_empty (Finset.subset_empty.1 h)
  rw [this]
  simp only [Finset.card_empty, Nat.cast_zero, Finset.card_singleton, Nat.cast_one, mul_one]
  exact pow_nonneg hq _

lemma good_nz {q : ℝ} (hq : 0 ≤ q) {Hs : Finset V} {O : Finset (Opt V)} (hO : Good q Hs O) :
    Good q Hs (nz O) := by
  unfold nz; split_ifs
  · exact hO
  · exact good_dflt hq

lemma good_ite {q : ℝ} {Hs : Finset V} {P : Prop} [Decidable P] {A B : Finset (Opt V)}
    (hA : Good q Hs A) (hB : Good q Hs B) : Good q Hs (if P then A else B) := by
  split_ifs
  · exact hA
  · exact hB

/-- Apex queries satisfy the ratio `(K/n)^|W|` (S05 (8), `r = 1`; zero for `r ≥ 2`). -/
lemma good_apex {K : ℝ} (hal : 0 < al) (hn : 0 < (Fintype.card V : ℝ)) (hK0 : 0 ≤ K)
    (hK : 2 ≤ K * al) (Hs : Finset V) (p q : V) (excl : Finset V) :
    Good (K / Fintype.card V) Hs (apexStep G lab F al p q excl) := by
  unfold apexStep
  split_ifs with hg
  · intro W hW _
    set s := apexSet G lab F p q excl
    obtain ⟨w, hw⟩ := hW
    have hsub : (s.image Sum.inl).filter (fun o => W ⊆ vsO o) ⊆ {Sum.inl w} := by
      intro o ho
      simp only [Finset.mem_filter, Finset.mem_image] at ho
      obtain ⟨⟨y, -, rfl⟩, hWy⟩ := ho
      simp only [vsO, Sum.elim_inl] at hWy
      have := Finset.mem_singleton.1 (hWy hw)
      simp [this]
    have hc : (((s.image Sum.inl).filter (fun o => W ⊆ vsO o)).card : ℝ) ≤ 1 := by
      exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
    have himg : ((s.image (Sum.inl : V → Opt V)).card : ℝ) = s.card := by
      rw [Finset.card_image_of_injective _ Sum.inl_injective]
    rw [himg]
    by_cases hW1 : W.card = 1
    · rw [hW1, pow_one]
      refine hc.trans ?_
      calc (1 : ℝ) ≤ K * al / 2 := by linarith
        _ = K / Fintype.card V * (al * Fintype.card V / 2) := by field_simp
        _ ≤ K / Fintype.card V * s.card := by gcongr
    · have hW2 : 2 ≤ W.card := by
        have := Finset.card_pos.2 ⟨w, hw⟩; omega
      have : (s.image Sum.inl).filter (fun o => W ⊆ vsO o) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun o ho hWo => ?_
        simp only [Finset.mem_image] at ho
        obtain ⟨y, -, rfl⟩ := ho
        simp only [vsO, Sum.elim_inl] at hWo
        have := Finset.card_le_card hWo
        simp at this; omega
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  · exact good_empty

/-- Hinge queries satisfy the ratio `(K/n)^|W|` (S05 (8), via `fresh_ratio`). -/
lemma good_hinge {K : ℝ} (hal : 0 < al) (hn : 0 < (Fintype.card V : ℝ)) (hK1 : 1 ≤ K)
    (hK : 2 ^ (hh.choose 2 + 1) / al ≤ K) (Hs : Finset V) (p q x y : V) :
    Good (K / Fintype.card V) Hs (hingeStep G lab F al hh p q x y Hs) := by
  unfold hingeStep
  split_ifs with hok
  · obtain ⟨d1, d2, d3, d4, d5, d6, hsub, h4, hle, hcard⟩ := hok
    intro W hW hWH
    rw [Finset.filter_image, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
    simp only [vsO, Sum.elim_inr]
    exact fresh_ratio d1 d2 d3 d4 d5 d6 hle h4 hal hK1 hK hn _ (Finset.filter_subset _ _) hcard
      W hW (Finset.disjoint_of_subset_right hsub hWH)
  · exact good_empty

variable (G lab F al hh u v a) in
/-- **Every query of the process satisfies S05 (8) for every history.** -/
theorem good_stepOpts {K : ℝ} (hal : 0 < al) (hn : 0 < (Fintype.card V : ℝ)) (hK1 : 1 ≤ K)
    (hK : 2 ^ (hh.choose 2 + 1) / al ≤ K) (k : ℕ) (g : ℕ → Opt V) (Hs : Finset V) :
    Good (K / Fintype.card V) Hs (stepOpts G lab F al hh u v a k g Hs) := by
  have hq : 0 ≤ K / (Fintype.card V : ℝ) := by positivity
  have hKa : 2 ≤ K * al := by
    have h1 : (2 : ℝ) ≤ 2 ^ (hh.choose 2 + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (hh.choose 2 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have := (div_le_iff₀ hal).1 hK
    linarith
  have hA := fun p q excl => good_apex (G := G) (lab := lab) (F := F) hal hn (by linarith) hKa Hs p q excl
  have hH := fun p q x y => good_hinge (G := G) (lab := lab) (F := F) (hh := hh) hal hn hK1 hK Hs p q x y
  match k with
  | 0 => exact hA _ _ _
  | 1 => exact hA _ _ _
  | 2 => exact hA _ _ _
  | 3 => exact hA _ _ _
  | 4 => exact hH _ _ _ _
  | 5 => exact hH _ _ _ _
  | 6 => exact good_ite (good_dflt hq) (hA _ _ _)
  | 7 => exact good_ite (good_dflt hq) (hH _ _ _ _)
  | 8 => exact good_ite (good_dflt hq) (hH _ _ _ _)
  | 9 => exact good_ite (good_dflt hq) (hA _ _ _)
  | 10 => exact good_ite (good_dflt hq) (hH _ _ _ _)
  | 11 => exact good_ite (good_dflt hq) (hH _ _ _ _)
  | k + 12 => exact good_dflt hq

variable (G lab F al hh u v a) in
/-- **First-arrival bound for one source** (S05 (9) with `B = E(T)`, 12 queries): a fixed set
`U` of at most three vertices outside `T` is covered by the revealed vertices with
probability `≤ (12 K / n)^|U|`. -/
theorem exposure_src {K : ℝ} (hal : 0 < al) (hn : 0 < (Fintype.card V : ℝ)) (hK1 : 1 ≤ K)
    (hK : 2 ^ (hh.choose 2 + 1) / al ≤ K) (U : Finset V) (hU : U.card ≤ 3)
    (hUT : Disjoint U {u, v, a}) :
    ∑ ω : Fin 12 → Opt V, Expo.wt (opts G lab F al hh u v a) 12 [] ω *
        (if U ⊆ Expo.aux vsO ω then 1 else 0) ≤
      (12 * K / Fintype.card V) ^ U.card := by
  have hq : 0 ≤ K / (Fintype.card V : ℝ) := by positivity
  have := Expo.exposure_bound (opts G lab F al hh u v a) (opts_nonempty G lab F al hh u v a)
    vsO (HS u v a) (HS_append u v a) hq 3
    (fun h W hW _ hWH => good_nz hq (good_stepOpts G lab F al hh u v a hal hn hK1 hK _ _ _) W hW hWH)
    12 [] U hU (by rwa [HS_nil])
  refine this.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring

end S10V23.Proc
