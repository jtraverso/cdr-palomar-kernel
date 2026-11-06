/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.Defs
public import CDRBicolour.Prefix.P2Types
public import CDRBicolour.Basic

/-!
# The CDR host for Paper III: hypotheses H3 (common neighbours) and H1 (diffuse seed)

The host of a profile `(a, b, c)`: the complete graph on `Fin (a+b+c)` labelled by the three
classes (`col3`), with allowed types the **bicoloured** multisets (`cdrF`: three labels, exactly
two distinct).  An allowed decomposition of all edges is a strictly bicoloured STS.

* `class_lower`: every class has at least `n/4 + 2` points once `n ≥ 400` (from the admissibility
  identity `(a-b)² + (b-c)² + (c-a)² = 2n`);
* `cdr_H3`: `CommonNbrCond` with `α = 1/4`;
* `cdr_H1`: `IsDiffuseSeed` with `C = 4`, for the type-uniform seed
  `w(XXY) = 1/(2|Y|)` corrected by `σ_A`, `σ_B`; the six edge equations hold, five identically
  and the `AB` one exactly by the admissibility identity.

Definitions `Host`, `IsAllowed`, `IsDiffuseSeed`, `CommonNbrCond` are those of Paper III
(`RequestProject.TypedTriangle.Defs`, imported from the Paper III library).
-/

@[expose] public section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- Allowed types: three labels, exactly two distinct. -/
def cdrF : Set (Multiset (Fin 3)) := {m | Multiset.card m = 3 ∧ m.toFinset.card = 2}

/-- The CDR host of a profile. -/
def cdrHost (a b c : ℕ) : Host (Fin (a + b + c)) (Fin 3) := ⟨⊤, col3 a b c⟩

/-! ### Class sizes -/

/-- Each class has at least `n/4 + 2` points, `n ≥ 400`. -/
theorem class_lower (x y z : ℕ)
    (e : (x : ℤ) ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z = x + y + z)
    (hn : 400 ≤ x + y + z) : x + y + z + 8 ≤ 4 * x := by
  by_contra hcon
  push Not at hcon
  have hn' : (400 : ℤ) ≤ x + y + z := by exact_mod_cast hn
  have hc : (4 : ℤ) * x < x + y + z + 8 := by exact_mod_cast hcon
  set s : ℤ := (y : ℤ) + z - 2 * x with hs
  have hs2 : s ^ 2 ≤ 4 * ((x : ℤ) + y + z) := by
    nlinarith [sq_nonneg ((y : ℤ) - z)]
  nlinarith

theorem class_lower_all {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    a + b + c + 8 ≤ 4 * a ∧ a + b + c + 8 ≤ 4 * b ∧ a + b + c + 8 ≤ 4 * c := by
  have e := h.2.2.2.2.1
  refine ⟨class_lower a b c e hn, ?_, ?_⟩
  · have := class_lower b a c (by push_cast; linear_combination e) (by omega); omega
  · have := class_lower c a b (by push_cast; linear_combination e) (by omega); omega

/-- Size of the class `k`. -/
theorem card_class (a b c : ℕ) (k : Fin 3) :
    (univ.filter fun w : Fin (a + b + c) => col3 a b c w = k).card =
      ![a, b, c] k := by
  fin_cases k
  · rw [← Fintype.card_subtype]; exact card_classA
  · rw [← Fintype.card_subtype]; exact card_classB
  · rw [← Fintype.card_subtype]; exact card_classC

/-! ### H3 -/

/-- **H3** for the CDR host, `α = 1/4`. -/
theorem cdr_H3 {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    CommonNbrCond (cdrHost a b c) cdrF (1 / 4) := by
  classical
  obtain ⟨ha, hb, hc⟩ := class_lower_all h hn
  intro u v _ k _
  set S := univ.filter fun w : Fin (a + b + c) => col3 a b c w = k with hS
  have hsz : a + b + c + 8 ≤ 4 * S.card := by
    rw [hS, card_class]
    fin_cases k <;> simp <;> omega
  have hsub : (S.erase u).erase v ⊆ commonNbrs (cdrHost a b c) k u v := by
    intro w hw
    simp only [mem_erase, hS, mem_filter, mem_univ, true_and] at hw
    simp only [commonNbrs, mem_filter, mem_univ, true_and, cdrHost, SimpleGraph.top_adj]
    exact ⟨Ne.symm hw.2.1, Ne.symm hw.1, hw.2.2⟩
  have h1 := card_le_card hsub
  have h2 := pred_card_le_card_erase (s := S.erase u) (a := v)
  have h3 := pred_card_le_card_erase (s := S) (a := u)
  have hle : a + b + c ≤ 4 * (commonNbrs (cdrHost a b c) k u v).card := by omega
  rw [Fintype.card_fin]
  have : ((a + b + c : ℕ) : ℝ) ≤ 4 * ((commonNbrs (cdrHost a b c) k u v).card : ℝ) := by
    exact_mod_cast hle
  linarith

/-! ### H1: edge sums over the complete host -/

section EdgeSum

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem val_map_triple (lab : V → I) {u v z : V} (huv : u ≠ v) (hzu : z ≠ u) (hzv : z ≠ v) :
    (({u, v, z} : Finset V).val.map lab) = ({lab u, lab v, lab z} : Multiset I) := by
  have h1 : v ∉ ({z} : Finset V) := by simp [Ne.symm hzv]
  have h2 : u ∉ ({v, z} : Finset V) := by simp [huv, Ne.symm hzu]
  rw [insert_val_of_notMem h2, insert_val_of_notMem h1]
  simp

open Classical in
/-- In the complete host, the allowed triangles through `uv` are the `{u, v, z}`. -/
theorem edge_sum_top (lab : V → I) (F : Set (Multiset I)) (g : Multiset I → ℝ) {u v : V}
    (huv : u ≠ v) :
    ∑ T ∈ (allowed (⟨⊤, lab⟩ : Host V I) F).filter (fun T => s(u, v) ∈ triEdges T),
        g (T.val.map lab) =
      ∑ z ∈ univ.filter (fun z => z ≠ u ∧ z ≠ v ∧ ({lab u, lab v, lab z} : Multiset I) ∈ F),
        g {lab u, lab v, lab z} := by
  classical
  have hset : (allowed (⟨⊤, lab⟩ : Host V I) F).filter (fun T => s(u, v) ∈ triEdges T) =
      (univ.filter fun z => z ≠ u ∧ z ≠ v ∧ ({lab u, lab v, lab z} : Multiset I) ∈ F).image
        (fun z => ({u, v, z} : Finset V)) := by
    ext T
    simp only [allowed, IsAllowed, triEdges, mem_filter, mem_univ, true_and, mem_image,
      mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff, SimpleGraph.top_adj]
    constructor
    · rintro ⟨⟨hT3, -, hF⟩, hsub, -⟩
      have hu : u ∈ T := hsub u (Or.inl rfl)
      have hv : v ∈ T := hsub v (Or.inr rfl)
      have hR : ((T.erase u).erase v).card = 1 := by
        rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm huv, hv⟩), card_erase_of_mem hu, hT3]
      obtain ⟨z, hz⟩ := card_eq_one.1 hR
      have hzm : z ∈ (T.erase u).erase v := by rw [hz]; exact mem_singleton_self z
      simp only [mem_erase] at hzm
      have hTe : T = {u, v, z} := by
        ext x
        simp only [mem_insert, mem_singleton]
        constructor
        · intro hx
          by_cases hxu : x = u
          · exact Or.inl hxu
          by_cases hxv : x = v
          · exact Or.inr (Or.inl hxv)
          have : x ∈ (T.erase u).erase v := by simp [hx, hxu, hxv]
          rw [hz, mem_singleton] at this
          exact Or.inr (Or.inr this)
        · rintro (rfl | rfl | rfl)
          · exact hu
          · exact hv
          · exact hzm.2.2
      refine ⟨z, ⟨hzm.2.1, hzm.1, ?_⟩, hTe.symm⟩
      rw [← val_map_triple lab huv hzm.2.1 hzm.1, ← hTe]; exact hF
    · rintro ⟨z, ⟨hzu, hzv, hF⟩, rfl⟩
      refine ⟨⟨?_, fun x _ y _ hxy => hxy, ?_⟩, ?_, huv⟩
      · rw [card_insert_of_notMem (by simp [huv, Ne.symm hzu]),
          card_insert_of_notMem (by simp [Ne.symm hzv]), card_singleton]
      · rw [val_map_triple lab huv hzu hzv]; exact hF
      · rintro x (rfl | rfl) <;> simp
  rw [hset, sum_image]
  · refine sum_congr rfl fun z hz => ?_
    simp only [mem_filter, mem_univ, true_and] at hz
    rw [val_map_triple lab huv hz.1 hz.2.1]
  · intro z hz z' hz' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hz hz'
    have h' : ({u, v, z} : Finset V) = {u, v, z'} := h
    have : z ∈ ({u, v, z'} : Finset V) := by rw [← h']; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact absurd h1 hz.1
    · exact absurd h1 hz.2.1
    · exact h1

open Classical in
/-- `edge_sum_top` for any finset with the same members (decidability instances may differ). -/
theorem edge_sum_top' (lab : V → I) (F : Set (Multiset I)) (g : Multiset I → ℝ) {u v : V}
    (huv : u ≠ v) (S : Finset (Finset V))
    (hS : ∀ T, T ∈ S ↔ T ∈ allowed (⟨⊤, lab⟩ : Host V I) F ∧ s(u, v) ∈ triEdges T) :
    ∑ T ∈ S, g (T.val.map lab) =
      ∑ z ∈ univ.filter (fun z => z ≠ u ∧ z ≠ v ∧ ({lab u, lab v, lab z} : Multiset I) ∈ F),
        g {lab u, lab v, lab z} := by
  have : S = (allowed (⟨⊤, lab⟩ : Host V I) F).filter (fun T => s(u, v) ∈ triEdges T) := by
    ext T; rw [hS, mem_filter]
  rw [this]; exact edge_sum_top lab F g huv

open Classical in
/-- Grouping the third vertex by its label. -/
theorem sum_by_label (lab : V → I) [Fintype I] (P : I → Prop) (g : I → ℝ)
    {u v : V} :
    ∑ z ∈ univ.filter (fun z => z ≠ u ∧ z ≠ v ∧ P (lab z)), g (lab z) =
      ∑ k, if P k then ((univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k).card : ℝ) * g k
        else 0 := by
  rw [← sum_fiberwise' (univ.filter fun z => z ≠ u ∧ z ≠ v ∧ P (lab z)) lab g]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_const, nsmul_eq_mul]
  split_ifs with hk
  · apply congrArg (fun s : Finset V => (s.card : ℝ) * g k)
    ext z; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3 ▸ hk⟩, h3⟩
  · rw [card_eq_zero.2, Nat.cast_zero, zero_mul]
    rw [filter_eq_empty_iff]; intro z hz hlab
    simp only [mem_filter, mem_univ, true_and] at hz
    exact hk (hlab ▸ hz.2.2)

/-- Points of the class `k` other than `u ≠ v`. -/
theorem card_third (lab : V → I) {u v : V} (huv : u ≠ v) (k : I) :
    ((univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k).card : ℝ) =
      ((univ.filter fun z => lab z = k).card : ℝ) - (if lab u = k then 1 else 0) -
        (if lab v = k then 1 else 0) := by
  set S := univ.filter fun z => lab z = k with hS
  have hset : (univ.filter fun z => z ≠ u ∧ z ≠ v ∧ lab z = k) = (S.erase u).erase v := by
    ext z; simp only [hS, mem_filter, mem_univ, true_and, mem_erase]; tauto
  rw [hset, card_erase_eq_ite, card_erase_eq_ite]
  have hv' : v ∈ S.erase u ↔ lab v = k := by
    simp [hS, mem_erase, Ne.symm huv]
  have hu' : u ∈ S ↔ lab u = k := by simp [hS]
  by_cases hu : lab u = k <;> by_cases hv : lab v = k
  · have h2 : 2 ≤ S.card := by
      have : ({u, v} : Finset V) ⊆ S := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hS, hu, hv]
      have := card_le_card this; rw [card_pair huv] at this; exact this
    rw [if_pos (hv'.2 hv), if_pos (hu'.2 hu), if_pos hu, if_pos hv, Nat.sub_sub,
      Nat.cast_sub h2]
    push_cast; ring
  · have h1 : 1 ≤ S.card := card_pos.2 ⟨u, hu'.2 hu⟩
    rw [if_neg (fun h => hv (hv'.1 h)), if_pos (hu'.2 hu), if_pos hu, if_neg hv,
      Nat.cast_sub h1]
    push_cast; ring
  · have h1 : 1 ≤ S.card := card_pos.2 ⟨v, by simp [hS, hv]⟩
    rw [if_pos (hv'.2 hv), if_neg (fun h => hu (hu'.1 h)), if_neg hu, if_pos hv,
      Nat.cast_sub h1]
    push_cast; ring
  · rw [if_neg (fun h => hv (hv'.1 h)), if_neg (fun h => hu (hu'.1 h)), if_neg hu, if_neg hv]
    ring

end EdgeSum

/-! ### H1: the seed -/

/-- Correction `σ_A`. -/
noncomputable def sigA (a c : ℝ) : ℝ := ((c - a) ^ 2 - c - a) / (2 * a * (a - 1))

/-- Correction `σ_B`. -/
noncomputable def sigB (b c : ℝ) : ℝ := -((b - c) ^ 2 - b - c) / (2 * b * (b - 1))

/-- The type-uniform seed weight. -/
noncomputable def wt (a b c : ℝ) (m : Multiset (Fin 3)) : ℝ :=
  if m.count 0 = 2 ∧ m.count 1 = 1 then (1 / 2 + sigA a c) / b
  else if m.count 0 = 2 ∧ m.count 2 = 1 then (1 / 2 - sigA a c) / c
  else if m.count 1 = 2 ∧ m.count 2 = 1 then (1 / 2 + sigB b c) / c
  else if m.count 1 = 2 ∧ m.count 0 = 1 then (1 / 2 - sigB b c) / a
  else if m.count 2 = 2 ∧ m.count 0 = 1 then 1 / (2 * a)
  else if m.count 2 = 2 ∧ m.count 1 = 1 then 1 / (2 * b)
  else 0

/-- The six allowed types, by their label counts. -/
theorem type_cases {m : Multiset (Fin 3)} (hm : m ∈ cdrF) :
    (m.count 0 = 2 ∧ m.count 1 = 1 ∧ m.count 2 = 0) ∨
    (m.count 0 = 2 ∧ m.count 1 = 0 ∧ m.count 2 = 1) ∨
    (m.count 0 = 0 ∧ m.count 1 = 2 ∧ m.count 2 = 1) ∨
    (m.count 0 = 1 ∧ m.count 1 = 2 ∧ m.count 2 = 0) ∨
    (m.count 0 = 1 ∧ m.count 1 = 0 ∧ m.count 2 = 2) ∨
    (m.count 0 = 0 ∧ m.count 1 = 1 ∧ m.count 2 = 2) := by
  obtain ⟨h3, h2⟩ := hm
  obtain ⟨x, y, z, rfl⟩ := Multiset.card_eq_three.1 h3
  revert h2
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- A weight between `1/(4N)` and `4/N`. -/
theorem wbound {Y N s : ℝ} (hY : N + 8 ≤ 4 * Y) (hYN : Y ≤ N) (hs : |s| ≤ 1 / 4) :
    1 / (4 * N) ≤ (1 / 2 + s) / Y ∧ (1 / 2 + s) / Y ≤ 4 / N := by
  rw [abs_le] at hs
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) hY0]; nlinarith
  · rw [div_le_div_iff₀ hY0 hN0]; nlinarith

theorem sig_bound {a b c : ℝ} (hadm : a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c = a + b + c)
    (hN : 400 ≤ a + b + c) (ha : a + b + c + 8 ≤ 4 * a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |((c - a) ^ 2 - c - a) / (2 * a * (a - 1))| ≤ 1 / 4 := by
  have hD : 0 < 2 * a * (a - 1) := by nlinarith
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, abs_le]
  have hca : (c - a) ^ 2 ≤ 2 * (a + b + c) := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
  constructor <;> nlinarith

/-- **H1** for the CDR host, `C = 4`. -/
theorem cdr_H1 {a b c : ℕ} (h : AdmissibleProfile a b c) (hn : 400 ≤ a + b + c) :
    IsDiffuseSeed (cdrHost a b c) cdrF 4
      (fun T => wt a b c (T.val.map (col3 a b c))) := by
  classical
  obtain ⟨ha4, hb4, hc4⟩ := class_lower_all h hn
  have hadmZ := h.2.2.2.2.1
  have hadm : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - a * b - a * c - b * c = a + b + c := by
    exact_mod_cast hadmZ
  have hN : (400 : ℝ) ≤ a + b + c := by exact_mod_cast hn
  have ha : (a : ℝ) + b + c + 8 ≤ 4 * a := by exact_mod_cast ha4
  have hb : (a : ℝ) + b + c + 8 ≤ 4 * b := by exact_mod_cast hb4
  have hc : (a : ℝ) + b + c + 8 ≤ 4 * c := by exact_mod_cast hc4
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hsA : |sigA a c| ≤ 1 / 4 := sig_bound hadm hN ha hb0 hc0
  have hsB : |sigB b c| ≤ 1 / 4 := by
    unfold sigB
    rw [neg_div, abs_neg, show ((b : ℝ) - c) ^ 2 - b - c = (c - b) ^ 2 - c - b by ring]
    exact sig_bound (a := (b : ℝ)) (b := (a : ℝ)) (c := (c : ℝ)) (by linear_combination hadm)
      (by linarith) (by linarith) ha0 hc0
  have hsA' : |-sigA a c| ≤ 1 / 4 := by rwa [abs_neg]
  have hsB' : |-sigB b c| ≤ 1 / 4 := by rwa [abs_neg]
  have h0 : |(0 : ℝ)| ≤ 1 / 4 := by norm_num
  have hcard : (Fintype.card (Fin (a + b + c)) : ℝ) = a + b + c := by simp
  let N_le : ℝ → Prop := fun Y => (a : ℝ) + b + c + 8 ≤ 4 * Y ∧ Y ≤ (a : ℝ) + b + c
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · -- bounds
    rw [hcard]
    have hm : T.val.map (col3 a b c) ∈ cdrF := hT.2.2
    have key : ∀ (x : ℝ) (Y : ℝ), N_le Y → wt a b c (T.val.map (col3 a b c)) = (1 / 2 + x) / Y →
        |x| ≤ 1 / 4 → (1 / (4 * ((a : ℝ) + b + c)) ≤ wt a b c (T.val.map (col3 a b c)) ∧
          wt a b c (T.val.map (col3 a b c)) ≤ 4 / ((a : ℝ) + b + c)) := by
      intro x Y hY hw hx; rw [hw]; exact wbound hY.1 hY.2 hx
    rcases type_cases hm with ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ |
      ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h0', h1', h2'⟩
    · exact key _ b ⟨hb, by linarith⟩ (by simp [wt, h0', h1', h2']) hsA
    · exact key _ c ⟨hc, by linarith⟩ (by simp [wt, h0', h1', h2', sub_eq_add_neg]) hsA'
    · exact key _ c ⟨hc, by linarith⟩ (by simp [wt, h0', h1', h2']) hsB
    · exact key _ a ⟨ha, by linarith⟩ (by simp [wt, h0', h1', h2', sub_eq_add_neg]) hsB'
    · exact key 0 a ⟨ha, by linarith⟩ (by simp [wt, h0', h1', h2']; ring) h0
    · exact key 0 b ⟨hb, by linarith⟩ (by simp [wt, h0', h1', h2']; ring) h0
  · -- edge sums
    induction e using Sym2.ind with
    | _ u v =>
    have huv : u ≠ v := he
    simp only [cdrHost]
    rw [edge_sum_top' (col3 a b c) cdrF (wt a b c) huv _ ?hS]
    case hS =>
      intro T
      convert (mem_filter (s := allowed (⟨⊤, col3 a b c⟩ : Host (Fin (a + b + c)) (Fin 3)) cdrF)
        (p := fun T => s(u, v) ∈ triEdges T) (a := T))
    rw [sum_by_label (col3 a b c) (fun k => ({col3 a b c u, col3 a b c v, k} :
      Multiset (Fin 3)) ∈ cdrF) (fun k => wt a b c {col3 a b c u, col3 a b c v, k})]
    simp only [card_third (col3 a b c) huv, card_class, Fin.sum_univ_three]
    have hA1 : (a : ℝ) - 1 ≠ 0 := by intro h'; linarith
    have hB1 : (b : ℝ) - 1 ≠ 0 := by intro h'; linarith
    have hC1 : (c : ℝ) - 1 ≠ 0 := by intro h'; linarith
    have hA : (a : ℝ) ≠ 0 := by intro h'; linarith
    have hB : (b : ℝ) ≠ 0 := by intro h'; linarith
    have hC : (c : ℝ) ≠ 0 := by intro h'; linarith
    generalize col3 a b c u = i
    generalize col3 a b c v = j
    fin_cases i <;> fin_cases j <;>
      simp (config := { decide := true }) [cdrF, wt, sigA, sigB] <;>
      field_simp <;> ring_nf <;> nlinarith [hadm]

/-! ### Bridge: an allowed decomposition of the CDR host is a realisation -/

/-- An allowed decomposition of all edges of the CDR host is a strictly bicoloured STS with
class sizes `a, b, c`. -/
theorem realises_of_decomposition {a b c : ℕ} (D : Finset (Finset (Fin (a + b + c))))
    (hD : IsDecomposition (cdrHost a b c) cdrF (edges (cdrHost a b c)) D) : Realises a b c := by
  classical
  obtain ⟨hall, hdisj, hcov⟩ := hD
  have hmem : ∀ T ∈ D, ∀ x y, x ≠ y → (s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T) := by
    intro T _ x y hxy
    simp [triEdges, mem_filter, mem_sym2_iff, Sym2.mem_iff, hxy]
  refine ⟨⟨D, fun T hT => (hall T hT).1, fun x y hxy => ?_⟩, col3 a b c, ?_, ?_, ?_, ?_⟩
  · have he : s(x, y) ∈ edges (cdrHost a b c) := by
      simp [edges, cdrHost, hxy]
    rw [← hcov] at he
    simp only [Finset.mem_biUnion] at he
    obtain ⟨T, hT, hxyT⟩ := he
    refine ⟨T, ⟨hT, (hmem T hT x y hxy).1 hxyT⟩, ?_⟩
    rintro T' ⟨hT', hx', hy'⟩
    by_contra hne
    have := hdisj hT' hT hne
    exact disjoint_left.1 this ((hmem T' hT' x y hxy).2 ⟨hx', hy'⟩) hxyT
  · intro T hT
    have h := (hall T hT).2.2
    exact h.2
  · rw [classSize, ← Fintype.card_subtype]; exact card_classA
  · rw [classSize, ← Fintype.card_subtype]; exact card_classB
  · rw [classSize, ← Fintype.card_subtype]; exact card_classC

end CDRBicolour.Absorption
