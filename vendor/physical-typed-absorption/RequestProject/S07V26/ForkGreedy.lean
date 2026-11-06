/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V26.ForkDegree

@[expose] public section

/-!
# V26 — the finite simultaneous greedy assignment of forks

Fixed data: a core `W`, an input edge set `X` (loopless), protected edges `P`, degree bounds
`degIn X ≤ r`, `degIn P ≤ b`, a saturation threshold `Q ≥ 1`, and a pool size `m` such that EVERY
permitted completion of every pair has at least `m` common neighbours inside `W` (the retained
H3 pools of the V25 core). `XZ X W` is the set of input edges with both ends outside `W`
(`|XZ| ≤ |X| ≤ n r / 2`).

**Window** (`hwin`, in integers, i.e. multiplied by `Q`):
`8·|XZ| + Q·(6 + 2·(b + 3r + Q + 4)) < Q·m`, the integer form of
`8I/Q + 6 + 2(b + 3r + Q + 4) < m`.

**Result** (`fork_greedy`): one fork per edge of `XZ`, valid over `W`, fork edge sets pairwise
disjoint and disjoint from `X ∪ P`; a root `x ∉ W` has fork degree `≤ 2·degIn X x ≤ 2r`, an
auxiliary `x ∈ W` has fork degree `≤ Q + 3`, hence `Δ(⋃ F_e) ≤ 2r + Q + 4`. The total auxiliary
use is `≤ 8|XZ|`, so at most `8|XZ|/Q` auxiliaries are ever saturated.

At each of the three successive choices (`w`, then `a`, then `b`) the forbidden vertices are:
saturated auxiliaries (`≤ 8|XZ|/Q`), and neighbours of the two relevant vertices through the
already-used graph `X ∪ P ∪ (earlier forks) ∪ (current partial fork)`, whose maximum degree is
`≤ D + 4` with `D = b + 3r + Q + 3`. Local repetitions (`a ≠ v`, `b ≠ u`, `b ≠ a`) are excluded
because they are neighbours through the partial fork. No `|Z|` term occurs.
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V25

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
  {W : Finset V}

/-- input edges with both ends outside the core -/
def XZ (X : Finset (Sym2 V)) (W : Finset V) : Finset (Sym2 V) :=
  X.filter (fun e => ∀ x ∈ e, x ∉ W)

/-- union of the fork edges over a set of root edges -/
def forkUnion (T : Finset (Sym2 V)) (fk : Sym2 V → Fork V) : Finset (Sym2 V) :=
  T.biUnion (fun e => (fk e).E)

/-- the fork system property: one valid fork per edge of `XZ X W`, pairwise edge-disjoint,
disjoint from `X ∪ P` -/
def ForkSystem (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (W : Finset V)
    (X P : Finset (Sym2 V)) (fk : Sym2 V → Fork V) : Prop :=
  (∀ e ∈ XZ X W, (fk e).root = e ∧ (fk e).Valid G lab F W) ∧
  (∀ e ∈ XZ X W, ∀ e' ∈ XZ X W, e ≠ e' → Disjoint (fk e).E (fk e').E) ∧
  (∀ e ∈ XZ X W, Disjoint (fk e).E (X ∪ P))

lemma mem_XZ {X : Finset (Sym2 V)} {e : Sym2 V} : e ∈ XZ X W ↔ e ∈ X ∧ ∀ x ∈ e, x ∉ W := by
  simp [XZ]

lemma XZ_subset (X : Finset (Sym2 V)) (W : Finset V) : XZ X W ⊆ X := filter_subset _ _

lemma mem_nbrIn {U : Finset (Sym2 V)} {x z : V} : z ∈ nbrIn U x ↔ s(x, z) ∈ U := by
  simp [nbrIn]

omit [Fintype V] in
/-- choosing a vertex of `A` outside three forbidden sets -/
lemma choose_avoid {A S N1 N2 : Finset V} (h : S.card + N1.card + N2.card < A.card) :
    ∃ z ∈ A, z ∉ S ∧ z ∉ N1 ∧ z ∉ N2 := by
  by_contra hc
  push_neg at hc
  have hsub : A ⊆ S ∪ N1 ∪ N2 := by
    intro z hz
    by_cases h1 : z ∈ S
    · simp [h1]
    by_cases h2 : z ∈ N1
    · simp [h2]
    · simp [hc z hz h1 h2]
  have := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  omega

/-- **one greedy step**: given an already-used edge set `U` of maximum degree `≤ D` and a
saturated set `S` with `|S| + 2D + 8 < m`, a root edge `uv` outside `W` that has a permitted
completion (`(link u).Adj v c`) receives a valid fork, edge-disjoint from `U`, whose
auxiliaries avoid `S`. -/
lemma fork_step {m : ℕ}
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      m ≤ ((commonNbrs G lab k u v) ∩ W).card)
    {U : Finset (Sym2 V)} {S : Finset V} {D : ℕ} (hU : ∀ x, degIn U x ≤ D)
    (hwin : S.card + 2 * D + 8 < m) {u v c : V} (huW : u ∉ W) (hvW : v ∉ W)
    (hadj : (link G lab F u).Adj v c) :
    ∃ f : Fork V, f.u = u ∧ f.v = v ∧ f.Valid G lab F W ∧ Disjoint f.E U ∧
      f.w ∉ S ∧ f.a ∉ S ∧ f.b ∉ S := by
  obtain ⟨huv, hF⟩ := link_root_ne hadj
  have hN : ∀ (U' : Finset (Sym2 V)) x, (nbrIn U' x).card ≤ degIn U' x := card_nbrIn_le
  -- choice of `w`
  obtain ⟨w, hwA, hwS, hwU, hwV⟩ := choose_avoid (A := (commonNbrs G lab (lab c) u v) ∩ W)
    (S := S) (N1 := nbrIn U u) (N2 := nbrIn U v) (by
      have := hpool u v huv _ hF
      have := (hN U u).trans (hU u); have := (hN U v).trans (hU v); omega)
  obtain ⟨hwc, hwW⟩ := mem_inter.1 hwA
  have h0 : (link G lab F u).Adj v w := commonNbr_link_adj hadj hwc
  obtain ⟨huw, hF2⟩ := link_root_ne h0.symm
  set U1 := insert s(u, w) (insert s(v, w) U) with hU1
  have hU1d : ∀ x, degIn U1 x ≤ D + 2 := fun x =>
    (degIn_insert_le _ _ x).trans (by have := (degIn_insert_le s(v, w) U x); have := hU x; omega)
  -- choice of `a`
  obtain ⟨a, haA, haS, haU, haW'⟩ := choose_avoid (A := (commonNbrs G lab (lab v) u w) ∩ W)
    (S := S) (N1 := nbrIn U1 u) (N2 := nbrIn U1 w) (by
      have := hpool u w huw _ hF2
      have := (hN U1 u).trans (hU1d u); have := (hN U1 w).trans (hU1d w); omega)
  obtain ⟨hac, haW⟩ := mem_inter.1 haA
  have h1 : (link G lab F u).Adj w a := commonNbr_link_adj h0.symm hac
  have h0' : (link G lab F v).Adj u w := ⟨huw, by rw [Finset.insert_comm]; exact h0.2⟩
  obtain ⟨hvw, hF3⟩ := link_root_ne h0'.symm
  set U2 := insert s(u, a) (insert s(a, w) U1) with hU2
  have hU2d : ∀ x, degIn U2 x ≤ D + 4 := fun x =>
    (degIn_insert_le _ _ x).trans
      (by have := (degIn_insert_le s(a, w) U1 x); have := hU1d x; omega)
  -- choice of `b`
  obtain ⟨b, hbA, hbS, hbU, hbW'⟩ := choose_avoid (A := (commonNbrs G lab (lab u) v w) ∩ W)
    (S := S) (N1 := nbrIn U2 v) (N2 := nbrIn U2 w) (by
      have := hpool v w hvw _ hF3
      have := (hN U2 v).trans (hU2d v); have := (hN U2 w).trans (hU2d w); omega)
  obtain ⟨hbc, hbW⟩ := mem_inter.1 hbA
  have h2 : (link G lab F v).Adj w b := commonNbr_link_adj h0'.symm hbc
  rw [mem_nbrIn] at hwU hwV haU haW' hbU hbW'
  have hab : a ≠ b := by
    rintro rfl
    exact hbW' (by rw [Sym2.eq_swap]; exact mem_insert_of_mem (mem_insert_self _ _))
  refine ⟨⟨u, v, w, a, b⟩, rfl, rfl, ⟨huW, hvW, hwW, haW, hbW, hab, h0.2, h1.2, h2.2⟩, ?_,
    hwS, haS, hbS⟩
  rw [Finset.disjoint_left]
  intro e he heU
  rw [Fork.mem_E] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at heU
  · exact hwU heU
  · exact hwV heU
  · exact haU (mem_insert_of_mem (mem_insert_of_mem heU))
  · exact haW' (by rw [Sym2.eq_swap]; exact mem_insert_of_mem (mem_insert_of_mem heU))
  · exact hbW' (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_insert_of_mem heU))))
  · exact hbU (by
      rw [Sym2.eq_swap]
      exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem heU))))

omit [Fintype V] in
/-- the root edge of an input edge with a permitted completion -/
lemma root_of_cover {e : Sym2 V} (h : ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T) :
    ∃ u v c : V, e = s(u, v) ∧ (link G lab F u).Adj v c := by
  obtain ⟨T, hT, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hu, hv, huv⟩ := mem_triEdges.1 he
    obtain ⟨c, hcu, hcv, rfl⟩ := eq_triple_of_mem hT.1 hu hv huv
    exact ⟨u, v, c, rfl, ⟨hcv.symm, hT⟩⟩

/-- **the greedy induction** over subsets `T ⊆ XZ X W` -/
theorem fork_greedy_aux {X P : Finset (Sym2 V)} {r b Q m : ℕ} (hQ : 1 ≤ Q)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      m ≤ ((commonNbrs G lab k u v) ∩ W).card)
    (hcov : ∀ e ∈ XZ X W, ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T)
    (hX : ∀ x, degIn X x ≤ r) (hP : ∀ x, degIn P x ≤ b)
    (hwin : 8 * (XZ X W).card + Q * (6 + 2 * (b + 3 * r + Q + 4)) < Q * m) :
    ∀ T ⊆ XZ X W, ∃ fk : Sym2 V → Fork V,
      (∀ e ∈ T, (fk e).root = e ∧ (fk e).Valid G lab F W) ∧
      (∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (fk e).E (fk e').E) ∧
      (∀ e ∈ T, Disjoint (fk e).E (X ∪ P)) ∧
      (∀ x, x ∉ W → degIn (forkUnion T fk) x ≤ 2 * degIn T x) ∧
      (∀ x ∈ W, degIn (forkUnion T fk) x ≤ Q + 3) ∧
      ∑ x ∈ W, degIn (forkUnion T fk) x ≤ 8 * T.card := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun e => ⟨(Quot.out e).1, (Quot.out e).1, (Quot.out e).1, (Quot.out e).1,
      (Quot.out e).1⟩, by simp, by simp, by simp, ?_, ?_, ?_⟩
    · intro x _; simp [forkUnion, degIn]
    · intro x _; simp [forkUnion, degIn]
    · simp [forkUnion, degIn]
  | insert e T heT ih =>
    intro hsub
    have heX : e ∈ XZ X W := hsub (mem_insert_self _ _)
    have hTX : T ⊆ XZ X W := (subset_insert _ _).trans hsub
    obtain ⟨fk, h1, h2, h3, h4, h5, h6⟩ := ih hTX
    set R := forkUnion T fk with hR
    set U := X ∪ P ∪ R with hUdef
    set S := W.filter (fun x => Q ≤ degIn R x) with hS
    set D := b + 3 * r + Q + 3 with hD
    have hRd : ∀ x, degIn R x ≤ 2 * r + Q + 3 := by
      intro x
      by_cases hx : x ∈ W
      · have := h5 x hx; omega
      · have := h4 x hx
        have := degIn_mono (hTX.trans (XZ_subset X W)) x
        have := hX x; omega
    have hU : ∀ x, degIn U x ≤ D := by
      intro x
      rw [hUdef]
      have := degIn_union_le (X ∪ P) R x
      have := degIn_union_le X P x
      have := hX x; have := hP x; have := hRd x; omega
    have hSsum : S.card * Q ≤ 8 * (XZ X W).card := by
      have e1 : S.card • Q ≤ ∑ x ∈ S, degIn R x :=
        card_nsmul_le_sum _ _ _ (fun x hx => (mem_filter.1 hx).2)
      have e2 : ∑ x ∈ S, degIn R x ≤ ∑ x ∈ W, degIn R x :=
        sum_le_sum_of_subset (filter_subset _ _)
      have e3 := card_le_card hTX
      rw [smul_eq_mul] at e1
      omega
    have hwin' : S.card + 2 * D + 8 < m := by
      have : Q * (S.card + 2 * D + 8) < Q * m := by
        have e : Q * (S.card + 2 * D + 8) =
            S.card * Q + Q * (6 + 2 * (b + 3 * r + Q + 4)) := by rw [hD]; ring
        rw [e]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    obtain ⟨u, v, c, rfl, hadj⟩ := root_of_cover (hcov _ heX)
    have huW : u ∉ W := (mem_XZ.1 heX).2 u (by simp)
    have hvW : v ∉ W := (mem_XZ.1 heX).2 v (by simp)
    obtain ⟨f, hfu, hfv, hf, hfU, hwS, haS, hbS⟩ :=
      fork_step hpool hU hwin' huW hvW hadj
    have hroot : f.root = s(u, v) := by rw [Fork.root, hfu, hfv]
    have hfR : Disjoint f.E R := hfU.mono_right subset_union_right
    have hfXP : Disjoint f.E (X ∪ P) := hfU.mono_right subset_union_left
    set fk' := Function.update fk s(u, v) f with hfk'
    have hfk'e : fk' s(u, v) = f := Function.update_self _ _ _
    have hfk'T : ∀ e' ∈ T, fk' e' = fk e' := fun e' he' =>
      Function.update_of_ne (fun h => heT (by rw [← h]; exact he')) _ _
    have hunion : forkUnion (insert s(u, v) T) fk' = f.E ∪ R := by
      rw [forkUnion, biUnion_insert, hfk'e, hR, forkUnion]
      congr 1
      exact biUnion_congr rfl fun e' he' => by rw [hfk'T e' he']
    have hsubR : ∀ e' ∈ T, (fk e').E ⊆ R := fun e' he' =>
      subset_biUnion_of_mem (fun e => (fk e).E) he'
    refine ⟨fk', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · rw [hfk'e]; exact ⟨hroot, hf⟩
      · rw [hfk'T e' he']; exact h1 e' he'
    · intro e' he' e'' he'' hne
      rcases mem_insert.1 he' with rfl | he' <;> rcases mem_insert.1 he'' with rfl | he''
      · exact absurd rfl hne
      · rw [hfk'e, hfk'T e'' he'']; exact hfR.mono_right (hsubR e'' he'')
      · rw [hfk'e, hfk'T e' he']; exact (hfR.mono_right (hsubR e' he')).symm
      · rw [hfk'T e' he', hfk'T e'' he'']; exact h2 e' he' e'' he'' hne
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · rw [hfk'e]; exact hfXP
      · rw [hfk'T e' he']; exact h3 e' he'
    · intro x hx
      rw [hunion, degIn_insert_of_notMem heT]
      have := degIn_union_le f.E R x
      have := hf.degIn_root hx
      rw [hroot] at this
      have := h4 x hx
      omega
    · intro x hx
      rw [hunion]
      have hle := degIn_union_le f.E R x
      have hb := hf.degIn_aux hx
      obtain ⟨-, -, -, -, -, -, -, hwa, hwb, hab⟩ := hf.distinct
      have hsat : ∀ y, y ∉ S → y ∈ W → degIn R y < Q := fun y hy hyW => by
        by_contra hc; exact hy (mem_filter.2 ⟨hyW, by omega⟩)
      by_cases hxw : x = f.w
      · rw [if_pos hxw, if_neg (by rw [hxw]; exact hwa), if_neg (by rw [hxw]; exact hwb)] at hb
        have := hsat x (hxw ▸ hwS) hx; omega
      by_cases hxa : x = f.a
      · rw [if_neg hxw, if_pos hxa, if_neg (by rw [hxa]; exact hab)] at hb
        have := hsat x (hxa ▸ haS) hx; omega
      by_cases hxb : x = f.b
      · rw [if_neg hxw, if_neg hxa, if_pos hxb] at hb
        have := hsat x (hxb ▸ hbS) hx; omega
      · rw [if_neg hxw, if_neg hxa, if_neg hxb] at hb
        have := h5 x hx; omega
    · rw [hunion, card_insert_of_notMem heT]
      calc ∑ x ∈ W, degIn (f.E ∪ R) x ≤ ∑ x ∈ W, (degIn f.E x + degIn R x) :=
            sum_le_sum fun x _ => degIn_union_le _ _ x
        _ = ∑ x ∈ W, degIn f.E x + ∑ x ∈ W, degIn R x := sum_add_distrib
        _ ≤ 8 + 8 * T.card := Nat.add_le_add hf.sum_degIn_W h6
        _ = 8 * (T.card + 1) := by ring

/-- **the simultaneous greedy fork assignment** (packaged). Under the integer window
`8|XZ| + Q(6 + 2(b + 3r + Q + 4)) < Q m`, there is ONE fork per edge of `XZ X W` forming a
`ForkSystem`, with root degree `≤ 2r`, auxiliary degree `≤ Q + 3`, maximum degree
`≤ 2r + Q + 4`, and at most `8|XZ|/Q` saturated auxiliaries. -/
theorem fork_greedy {X P : Finset (Sym2 V)} {r b Q m : ℕ} (hQ : 1 ≤ Q)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      m ≤ ((commonNbrs G lab k u v) ∩ W).card)
    (hcov : ∀ e ∈ XZ X W, ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T)
    (hX : ∀ x, degIn X x ≤ r) (hP : ∀ x, degIn P x ≤ b)
    (hwin : 8 * (XZ X W).card + Q * (6 + 2 * (b + 3 * r + Q + 4)) < Q * m) :
    ∃ fk : Sym2 V → Fork V, ForkSystem G lab F W X P fk ∧
      (∀ x, x ∉ W → degIn (forkUnion (XZ X W) fk) x ≤ 2 * r) ∧
      (∀ x ∈ W, degIn (forkUnion (XZ X W) fk) x ≤ Q + 3) ∧
      (∀ x, degIn (forkUnion (XZ X W) fk) x ≤ 2 * r + Q + 4) ∧
      (W.filter fun x => Q ≤ degIn (forkUnion (XZ X W) fk) x).card * Q ≤ 8 * (XZ X W).card := by
  obtain ⟨fk, h1, h2, h3, h4, h5, h6⟩ :=
    fork_greedy_aux hQ hpool hcov hX hP hwin (XZ X W) subset_rfl
  have hroot : ∀ x, x ∉ W → degIn (forkUnion (XZ X W) fk) x ≤ 2 * r := fun x hx => by
    have := h4 x hx; have := degIn_mono (XZ_subset X W) x; have := hX x; omega
  refine ⟨fk, ⟨h1, h2, h3⟩, hroot, h5, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ W
    · have := h5 x hx; omega
    · have := hroot x hx; omega
  · have e1 := card_nsmul_le_sum (W.filter fun x => Q ≤ degIn (forkUnion (XZ X W) fk) x)
      (fun x => degIn (forkUnion (XZ X W) fk) x) Q (fun x hx => (mem_filter.1 hx).2)
    have e2 := sum_le_sum_of_subset (f := fun x => degIn (forkUnion (XZ X W) fk) x)
      (filter_subset (fun x => Q ≤ degIn (forkUnion (XZ X W) fk) x) W)
    rw [smul_eq_mul] at e1
    beta_reduce at e1 e2
    omega

end S07V26

end
