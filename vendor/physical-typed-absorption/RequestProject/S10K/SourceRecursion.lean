/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.OneEdge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23 / S05 §2 with `B = E(T)`: the recursion for one source triangle

Source `T = {u, v, a}`; `B` is EXACTLY the three edges of `T`. Pivot apices `b1, b2, b3`
for the edges `uv, ua, va`; bridge `c` for `uv`; hinges `J1` (roots `u,v,a,c`) and
`J2` (roots `u,v,c,b1`). In the fixed mode `D_a(J1)` exactly one triangle `Q1` contains
`ua` and one `Q2` contains `va` (`cover_facts`); they are replaced by one-deleted-edge
transports (`OneEdge.lean`) to the pivots `ua b2`, `va b3` with bridges `c1`, `c2` and hinges
`J3, J4`, `J5, J6` (or by nothing if `Q1` already is the pivot).

* `mainStep` : `A mvec = χ_T − χ_(uv b1) − χ_(Q1) − χ_(Q2)` and `mvec` avoids `T`.
* `srcCert_spec` (under `SrcValid`): `A c = χ_T − χ_P1 − χ_P2 − χ_P3`, and `c` vanishes on
  every triangle sharing two vertices with `T`.
* `srcCert_abs_le` (`|c(S)| ≤ 14`), `srcCert_supp` (support on permitted triangles) and
  `srcCert_verts` (every vertex of a support triangle lies in `T` or in the revealed
  vertices) hold for ALL choices.

The validity hypotheses `SrcValid` are deterministic; they are produced by the random
process at every positive-probability outcome (`SourceProcess.lean`).
-/

open Finset

noncomputable section
open Classical

namespace S10V23

open TypedTriangle.SparseEdge S10V22

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- `D_a(J1)`: the fixed mode of `J1` containing the wedge of `a`. -/
@[irreducible] def dA (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (J1 : Finset (Sym2 V)) : Finset (Finset V) := decOf G lab F (J1 ∪ wedge u v a)

/-- The main step vector `D_a − Q1 − Q2 − D_c + E_c − E_b`. -/
def mvec (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a c b : V)
    (J1 J2 : Finset (Sym2 V)) : Finset V → ℝ :=
  decVec (dA G lab F u v a J1) - decVec ((dA G lab F u v a J1).filter (fun S => s(u, a) ∈ edgesOf S))
    - decVec ((dA G lab F u v a J1).filter (fun S => s(v, a) ∈ edgesOf S))
    - decVec (decOf G lab F (J1 ∪ wedge u v c)) +
    (decVec (decOf G lab F (J2 ∪ wedge u v c)) - decVec (decOf G lab F (J2 ∪ wedge u v b)))

/-- `Q1`, `Q2` and their third vertices. -/
@[irreducible] def Q1 (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (J1 : Finset (Sym2 V)) : Finset V := cover (dA G lab F u v a J1) s(u, a)
@[irreducible] def Q2 (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (J1 : Finset (Sym2 V)) : Finset V := cover (dA G lab F u v a J1) s(v, a)
@[irreducible] def x1 (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (J1 : Finset (Sym2 V)) : V := third (Q1 G lab F u v a J1) u a
@[irreducible] def x2 (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (u v a : V)
    (J1 : Finset (Sym2 V)) : V := third (Q2 G lab F u v a J1) v a

lemma dA_eq (u v a : V) (J1 : Finset (Sym2 V)) :
    dA G lab F u v a J1 = decOf G lab F (J1 ∪ wedge u v a) := by unfold dA; rfl
lemma Q1_eq (u v a : V) (J1 : Finset (Sym2 V)) :
    Q1 G lab F u v a J1 = cover (decOf G lab F (J1 ∪ wedge u v a)) s(u, a) := by
  unfold Q1; rw [dA_eq]
lemma Q2_eq (u v a : V) (J1 : Finset (Sym2 V)) :
    Q2 G lab F u v a J1 = cover (decOf G lab F (J1 ∪ wedge u v a)) s(v, a) := by
  unfold Q2; rw [dA_eq]
lemma x1_eq (u v a : V) (J1 : Finset (Sym2 V)) :
    x1 G lab F u v a J1 = third (Q1 G lab F u v a J1) u a := by unfold x1; rfl
lemma x2_eq (u v a : V) (J1 : Finset (Sym2 V)) :
    x2 G lab F u v a J1 = third (Q2 G lab F u v a J1) v a := by unfold x2; rfl

omit [Fintype V] in
lemma triple_comm1 (u v a : V) : ({u, a, v} : Finset V) = {u, v, a} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

omit [Fintype V] in
lemma triple_comm2 (u v a : V) : ({v, a, u} : Finset V) = {u, v, a} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- Facts on `Q1`, `Q2` from the hinge `J1`. -/
theorem Q_facts {u v a c : V} {J1 : Finset (Sym2 V)} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a)
    (hJ1 : IsHinge G lab F u v a c J1) :
    (Q1 G lab F u v a J1 ∈ dA G lab F u v a J1 ∧
      (dA G lab F u v a J1).filter (fun S => s(u, a) ∈ edgesOf S) = {Q1 G lab F u v a J1} ∧
      v ∉ Q1 G lab F u v a J1 ∧ IsAllowed G lab F (Q1 G lab F u v a J1) ∧
      x1 G lab F u v a J1 ∉ ({u, v, a} : Finset V) ∧
      Q1 G lab F u v a J1 = {u, a, x1 G lab F u v a J1}) ∧
    (Q2 G lab F u v a J1 ∈ dA G lab F u v a J1 ∧
      (dA G lab F u v a J1).filter (fun S => s(v, a) ∈ edgesOf S) = {Q2 G lab F u v a J1} ∧
      u ∉ Q2 G lab F u v a J1 ∧ IsAllowed G lab F (Q2 G lab F u v a J1) ∧
      x2 G lab F u v a J1 ∉ ({u, v, a} : Finset V) ∧
      Q2 G lab F u v a J1 = {v, a, x2 G lab F u v a J1}) := by
  rw [x1_eq, x2_eq, Q1_eq, Q2_eq, dA_eq]
  have hD := decOf_spec (G := G) (lab := lab) (F := F) hJ1.2.2.1
  have huvX : s(u, v) ∉ J1 ∪ wedge u v a := by
    simp only [Finset.mem_union, not_or]
    exact ⟨not_mem_hinge_uv hJ1 huv, not_mem_wedge_uv huv hua hva⟩
  have h1 := cover_facts hD hua huv (Ne.symm hva) (by simp [wedge]) huvX
  have h2 := cover_facts hD hva (Ne.symm huv) (Ne.symm hua) (by simp [wedge])
    (by rwa [Sym2.eq_swap])
  obtain ⟨a1, -, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, -, b3, b4, b5, b6, b7⟩ := h2
  refine ⟨⟨a1, a3, a4, a5, ?_, a7⟩, ⟨b1, b3, b4, b5, ?_, b7⟩⟩
  · rw [← triple_comm1]; exact a6
  · rw [← triple_comm2]; exact b6

/-- **Main step of the recursion.** -/
theorem mainStep {u v a c b : V} {J1 J2 : Finset (Sym2 V)} (hT : IsAllowed G lab F {u, v, a})
    (hcT : c ∉ ({u, v, a} : Finset V)) (hbT : b ∉ ({u, v, a} : Finset V))
    (hJ1 : IsHinge G lab F u v a c J1) (hJ2 : IsHinge G lab F u v c b J2)
    (haJ2 : a ∉ support J2) :
    Aop G lab F (mvec G lab F u v a c b J1 J2) = chiR (edgesOf {u, v, a}) -
        chiR (edgesOf {u, v, b}) - chiR (edgesOf (Q1 G lab F u v a J1)) -
        chiR (edgesOf (Q2 G lab F u v a J1)) ∧
      ∀ S, 2 ≤ (S ∩ {u, v, a}).card → mvec G lab F u v a c b J1 J2 S = 0 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hT.1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcT hbT
  obtain ⟨hcu, hcv, hca⟩ := hcT
  obtain ⟨hbu, hbv, hba⟩ := hbT
  obtain ⟨⟨hQ1, hf1, hvQ1, hQ1a, -, -⟩, ⟨hQ2, hf2, huQ2, hQ2a, -, -⟩⟩ :=
    Q_facts huv hua hva hJ1 (G := G) (lab := lab) (F := F)
  have hDa : IsDecomposition G lab F (J1 ∪ wedge u v a) (dA G lab F u v a J1) := by
    rw [dA_eq]; exact decOf_spec hJ1.2.2.1
  refine ⟨?_, fun S hS => ?_⟩
  · have e1 := A_hinge hJ1 huv hua hva (Ne.symm hcu) (Ne.symm hcv) hDa (decOf_spec hJ1.2.2.2)
    have e2 := A_hinge hJ2 huv (Ne.symm hcu) (Ne.symm hcv) (Ne.symm hbu) (Ne.symm hbv)
      (decOf_spec hJ2.2.2.1) (decOf_spec hJ2.2.2.2)
    have e3 : Aop G lab F (decVec ((dA G lab F u v a J1).filter
        (fun S => s(u, a) ∈ edgesOf S))) = chiR (edgesOf (Q1 G lab F u v a J1)) := by
      rw [hf1, decVec_singleton]; exact A_single hQ1a
    have e4 : Aop G lab F (decVec ((dA G lab F u v a J1).filter
        (fun S => s(v, a) ∈ edgesOf S))) = chiR (edgesOf (Q2 G lab F u v a J1)) := by
      rw [hf2, decVec_singleton]; exact A_single hQ2a
    have : mvec G lab F u v a c b J1 J2 = (decVec (dA G lab F u v a J1) -
        decVec (decOf G lab F (J1 ∪ wedge u v c))) -
        decVec ((dA G lab F u v a J1).filter (fun S => s(u, a) ∈ edgesOf S)) -
        decVec ((dA G lab F u v a J1).filter (fun S => s(v, a) ∈ edgesOf S)) +
        (decVec (decOf G lab F (J2 ∪ wedge u v c)) -
          decVec (decOf G lab F (J2 ∪ wedge u v b))) := by
      unfold mvec; abel
    rw [this, map_add, map_sub, map_sub, e1, e2, e3, e4]
    abel
  · -- triangles of the three modes missing `E(T)`
    have hJ1d := disjoint_hinge_left hJ1
    have hJ2d : Disjoint J2 (edgesOf {u, v, a}) :=
      disjoint_of_avoid (not_mem_hinge_uv hJ2 huv) haJ2
    have nc : c ∉ ({u, v, a} : Finset V) := by simp [hcu, hcv, hca]
    have nb : b ∉ ({u, v, a} : Finset V) := by simp [hbu, hbv, hba]
    have z1 := decVec_decOf_eq_zero (G := G) (lab := lab) (F := F)
      (disjoint_union_wedge (p := u) (q := v) hJ1d nc) hS
    have z2 := decVec_decOf_eq_zero (G := G) (lab := lab) (F := F)
      (disjoint_union_wedge (p := u) (q := v) hJ2d nc) hS
    have z3 := decVec_decOf_eq_zero (G := G) (lab := lab) (F := F)
      (disjoint_union_wedge (p := u) (q := v) hJ2d nb) hS
    -- the mode `D_a`
    have za : decVec (dA G lab F u v a J1) S -
        decVec ((dA G lab F u v a J1).filter (fun S => s(u, a) ∈ edgesOf S)) S -
        decVec ((dA G lab F u v a J1).filter (fun S => s(v, a) ∈ edgesOf S)) S = 0 := by
      rw [hf1, hf2]
      by_cases hSD : S ∈ dA G lab F u v a J1
      · obtain ⟨x, y, hxy, hxS, hyS, hxT, hyT⟩ := exists_edge_of_two_le hS
        have hxyX : s(x, y) ∈ J1 ∪ wedge u v a :=
          edgesOf_subset_of_mem_dec hDa hSD (mem_edgesOf.2 ⟨hxS, hyS, hxy⟩)
        have hxyJ : s(x, y) ∉ J1 := fun h =>
          Finset.disjoint_left.1 hJ1d h (mem_edgesOf.2 ⟨hxT, hyT, hxy⟩)
        have hw : s(x, y) ∈ wedge u v a := by
          rcases Finset.mem_union.1 hxyX with h | h
          · exact absurd h hxyJ
          · exact h
        have hSe : s(u, a) ∈ edgesOf S ∨ s(v, a) ∈ edgesOf S := by
          simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with h | h
          · left; rw [← h]; exact mem_edgesOf.2 ⟨hxS, hyS, hxy⟩
          · right; rw [← h]; exact mem_edgesOf.2 ⟨hxS, hyS, hxy⟩
        have hQne : Q1 G lab F u v a J1 ≠ Q2 G lab F u v a J1 := by
          intro h
          have : s(v, a) ∈ edgesOf (Q2 G lab F u v a J1) := by
            have := (Finset.ext_iff.1 hf2 (Q2 G lab F u v a J1)).2 (Finset.mem_singleton_self _)
            exact (Finset.mem_filter.1 this).2
          rw [← h] at this
          exact hvQ1 (mem_edgesOf.1 this).1
        rcases hSe with h | h
        · have hS1 : S = Q1 G lab F u v a J1 := by
            have := (Finset.ext_iff.1 hf1 S).1 (Finset.mem_filter.2 ⟨hSD, h⟩)
            exact Finset.mem_singleton.1 this
          subst hS1
          simp [decVec, hSD, hQne]
        · have hS2 : S = Q2 G lab F u v a J1 := by
            have := (Finset.ext_iff.1 hf2 S).1 (Finset.mem_filter.2 ⟨hSD, h⟩)
            exact Finset.mem_singleton.1 this
          subst hS2
          simp [decVec, hSD, Ne.symm hQne]
      · have h1 : S ≠ Q1 G lab F u v a J1 := fun h => hSD (h ▸ hQ1)
        have h2 : S ≠ Q2 G lab F u v a J1 := fun h => hSD (h ▸ hQ2)
        simp [decVec, hSD, h1, h2]
    unfold mvec
    simp only [Pi.add_apply, Pi.sub_apply, z1, z2, z3]
    linarith

/-! ## The full certificate of one source -/

/-- Deterministic validity of the choices for the source `T = {u,v,a}`. -/
structure SrcValid (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (u v a b1 b2 b3 c c1 c2 : V) (J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)) : Prop where
  hT : IsAllowed G lab F {u, v, a}
  hb1 : IsAllowed G lab F {u, v, b1}
  hb1a : b1 ≠ a
  hb2 : IsAllowed G lab F {u, a, b2}
  hb2v : b2 ≠ v
  hb3 : IsAllowed G lab F {v, a, b3}
  hb3u : b3 ≠ u
  hcT : c ∉ ({u, v, a} : Finset V)
  hJ1 : IsHinge G lab F u v a c J1
  hJ2 : IsHinge G lab F u v c b1 J2
  haJ2 : a ∉ support J2
  ht1 : x1 G lab F u v a J1 ≠ b2 → c1 ∉ ({u, v, a} : Finset V) ∧
    IsHinge G lab F u a (x1 G lab F u v a J1) c1 J3 ∧ v ∉ support J3 ∧
    IsHinge G lab F u a c1 b2 J4 ∧ v ∉ support J4
  ht2 : x2 G lab F u v a J1 ≠ b3 → c2 ∉ ({u, v, a} : Finset V) ∧
    IsHinge G lab F v a (x2 G lab F u v a J1) c2 J5 ∧ u ∉ support J5 ∧
    IsHinge G lab F v a c2 b3 J6 ∧ u ∉ support J6

/-- The certificate of the source `T = {u,v,a}`. -/
def srcCert (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (u v a b1 b2 b3 c c1 c2 : V) (J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)) : Finset V → ℝ :=
  mvec G lab F u v a c b1 J1 J2 +
    (if x1 G lab F u v a J1 = b2 then 0 else tvec G lab F J3 J4 u a (x1 G lab F u v a J1) c1 b2) +
    (if x2 G lab F u v a J1 = b3 then 0 else tvec G lab F J5 J6 v a (x2 G lab F u v a J1) c2 b3)

/-- **The recursion for the source triangle.** -/
theorem srcCert_spec {u v a b1 b2 b3 c c1 c2 : V} {J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)}
    (hv : SrcValid G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6) :
    Aop G lab F (srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6) =
        chiR (edgesOf {u, v, a}) - chiR (edgesOf {u, v, b1}) - chiR (edgesOf {u, a, b2}) -
          chiR (edgesOf {v, a, b3}) ∧
      ∀ S, 2 ≤ (S ∩ {u, v, a}).card →
        srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 S = 0 := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hv.hT.1
  have hb1T : b1 ∉ ({u, v, a} : Finset V) := by
    obtain ⟨-, h2, h3⟩ := distinct_of_card_three hv.hb1.1
    simp [Ne.symm h2, Ne.symm h3, hv.hb1a]
  have hb2T : b2 ∉ ({u, a, v} : Finset V) := by
    obtain ⟨-, h2, h3⟩ := distinct_of_card_three hv.hb2.1
    simp [Ne.symm h2, Ne.symm h3, hv.hb2v]
  have hb3T : b3 ∉ ({v, a, u} : Finset V) := by
    obtain ⟨-, h2, h3⟩ := distinct_of_card_three hv.hb3.1
    simp [Ne.symm h2, Ne.symm h3, hv.hb3u]
  obtain ⟨hm1, hm2⟩ := mainStep hv.hT hv.hcT hb1T hv.hJ1 hv.hJ2 hv.haJ2
  obtain ⟨⟨-, -, -, -, hx1T, hQ1eq⟩, ⟨-, -, -, -, hx2T, hQ2eq⟩⟩ :=
    Q_facts huv hua hva hv.hJ1 (G := G) (lab := lab) (F := F)
  -- the two transports
  have ht1 : Aop G lab F (if x1 G lab F u v a J1 = b2 then 0 else
        tvec G lab F J3 J4 u a (x1 G lab F u v a J1) c1 b2) =
        chiR (edgesOf (Q1 G lab F u v a J1)) - chiR (edgesOf {u, a, b2}) ∧
      ∀ S, 2 ≤ (S ∩ {u, v, a}).card → (if x1 G lab F u v a J1 = b2 then 0 else
        tvec G lab F J3 J4 u a (x1 G lab F u v a J1) c1 b2) S = 0 := by
    split_ifs with hs
    · refine ⟨?_, fun _ _ => rfl⟩
      rw [map_zero, hQ1eq, hs, sub_self]
    · obtain ⟨hc1T, hJ3, hvJ3, hJ4, hvJ4⟩ := hv.ht1 hs
      have hx : x1 G lab F u v a J1 ∉ ({u, a, v} : Finset V) := by rwa [triple_comm1]
      have hc : c1 ∉ ({u, a, v} : Finset V) := by rwa [triple_comm1]
      obtain ⟨e1, e2⟩ := oneEdge_transport hua hx hc hb2T hJ3 hvJ3 hJ4 hvJ4
      refine ⟨by rw [e1, hQ1eq], fun S hS => e2 S (by rwa [triple_comm1])⟩
  have ht2 : Aop G lab F (if x2 G lab F u v a J1 = b3 then 0 else
        tvec G lab F J5 J6 v a (x2 G lab F u v a J1) c2 b3) =
        chiR (edgesOf (Q2 G lab F u v a J1)) - chiR (edgesOf {v, a, b3}) ∧
      ∀ S, 2 ≤ (S ∩ {u, v, a}).card → (if x2 G lab F u v a J1 = b3 then 0 else
        tvec G lab F J5 J6 v a (x2 G lab F u v a J1) c2 b3) S = 0 := by
    split_ifs with hs
    · refine ⟨?_, fun _ _ => rfl⟩
      rw [map_zero, hQ2eq, hs, sub_self]
    · obtain ⟨hc2T, hJ5, huJ5, hJ6, huJ6⟩ := hv.ht2 hs
      have hx : x2 G lab F u v a J1 ∉ ({v, a, u} : Finset V) := by rwa [triple_comm2]
      have hc : c2 ∉ ({v, a, u} : Finset V) := by rwa [triple_comm2]
      obtain ⟨e1, e2⟩ := oneEdge_transport hva hx hc hb3T hJ5 huJ5 hJ6 huJ6
      refine ⟨by rw [e1, hQ2eq], fun S hS => e2 S (by rwa [triple_comm2])⟩
  refine ⟨?_, fun S hS => ?_⟩
  · unfold srcCert
    rw [map_add, map_add, hm1, ht1.1, ht2.1]
    abel
  · unfold srcCert
    simp only [Pi.add_apply, hm2 S hS, ht1.2 S hS, ht2.2 S hS, add_zero]

/-! ## Properties valid for every choice -/

omit [Fintype V] in
lemma decVec_mem {D : Finset (Finset V)} {S : Finset V} (h : decVec D S ≠ 0) : S ∈ D := by
  by_contra hS; exact h (decVec_eq_zero hS)

omit [Fintype V] in
lemma decVec_nonneg (D : Finset (Finset V)) (S : Finset V) : 0 ≤ decVec D S := by
  unfold decVec; split_ifs <;> norm_num

omit [Fintype V] in
lemma decVec_le_one (D : Finset (Finset V)) (S : Finset V) : decVec D S ≤ 1 := by
  unfold decVec; split_ifs <;> norm_num

/-- The edge sets whose fixed decompositions appear in the certificate. -/
def certSets (u v a b1 b2 b3 c c1 c2 : V) (J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)) (x y : V) :
    List (Finset (Sym2 V)) :=
  [J1 ∪ wedge u v a, J1 ∪ wedge u v c, J2 ∪ wedge u v c, J2 ∪ wedge u v b1,
    J3 ∪ wedge u a x, J3 ∪ wedge u a c1, J4 ∪ wedge u a c1, J4 ∪ wedge u a b2,
    J5 ∪ wedge v a y, J5 ∪ wedge v a c2, J6 ∪ wedge v a c2, J6 ∪ wedge v a b3]

/-- A triangle in the support of the certificate is a triangle of one of the fixed
decompositions. -/
lemma srcCert_ne_zero {u v a b1 b2 b3 c c1 c2 : V} {J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)}
    {S : Finset V} (h : srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 S ≠ 0) :
    ∃ X ∈ certSets u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 (x1 G lab F u v a J1)
      (x2 G lab F u v a J1), S ∈ decOf G lab F X := by
  by_contra hno
  push_neg at hno
  apply h
  have z : ∀ X ∈ certSets u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 (x1 G lab F u v a J1)
      (x2 G lab F u v a J1), decVec (decOf G lab F X) S = 0 := fun X hX =>
    decVec_eq_zero (hno X hX)
  simp only [certSets, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at z
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12⟩ := z
  rw [← dA_eq] at z1
  have f1 : decVec ((dA G lab F u v a J1).filter (fun S => s(u, a) ∈ edgesOf S)) S = 0 :=
    decVec_eq_zero fun hm => by
      have : decVec (dA G lab F u v a J1) S = 1 := by
        simp [decVec, (Finset.mem_filter.1 hm).1]
      rw [z1] at this; norm_num at this
  have f2 : decVec ((dA G lab F u v a J1).filter (fun S => s(v, a) ∈ edgesOf S)) S = 0 :=
    decVec_eq_zero fun hm => by
      have : decVec (dA G lab F u v a J1) S = 1 := by
        simp [decVec, (Finset.mem_filter.1 hm).1]
      rw [z1] at this; norm_num at this
  unfold srcCert mvec tvec
  split_ifs <;> simp [z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, f1, f2]

omit [Fintype V] in
lemma decVec_mem01 (D : Finset (Finset V)) (S : Finset V) : 0 ≤ decVec D S ∧ decVec D S ≤ 1 :=
  ⟨decVec_nonneg D S, decVec_le_one D S⟩

lemma abs_tvec_le (J J' : Finset (Sym2 V)) (p q x y b : V) (S : Finset V) :
    |tvec G lab F J J' p q x y b S| ≤ 4 := by
  unfold tvec
  simp only [Pi.add_apply, Pi.sub_apply]
  obtain ⟨a1, a2⟩ := decVec_mem01 (decOf G lab F (J ∪ wedge p q x)) S
  obtain ⟨b1, b2⟩ := decVec_mem01 (decOf G lab F (J ∪ wedge p q y)) S
  obtain ⟨c1, c2⟩ := decVec_mem01 (decOf G lab F (J' ∪ wedge p q y)) S
  obtain ⟨d1, d2⟩ := decVec_mem01 (decOf G lab F (J' ∪ wedge p q b)) S
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma abs_mvec_le (u v a c b : V) (J1 J2 : Finset (Sym2 V)) (S : Finset V) :
    |mvec G lab F u v a c b J1 J2 S| ≤ 6 := by
  unfold mvec
  simp only [Pi.add_apply, Pi.sub_apply]
  obtain ⟨a1, a2⟩ := decVec_mem01 (dA G lab F u v a J1) S
  obtain ⟨b1, b2⟩ := decVec_mem01 ((dA G lab F u v a J1).filter
    (fun S => s(u, a) ∈ edgesOf S)) S
  obtain ⟨c1, c2⟩ := decVec_mem01 ((dA G lab F u v a J1).filter
    (fun S => s(v, a) ∈ edgesOf S)) S
  obtain ⟨d1, d2⟩ := decVec_mem01 (decOf G lab F (J1 ∪ wedge u v c)) S
  obtain ⟨e1, e2⟩ := decVec_mem01 (decOf G lab F (J2 ∪ wedge u v c)) S
  obtain ⟨f1, f2⟩ := decVec_mem01 (decOf G lab F (J2 ∪ wedge u v b)) S
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Pointwise bound** `|c(S)| ≤ 14`. -/
lemma srcCert_abs_le (u v a b1 b2 b3 c c1 c2 : V) (J1 J2 J3 J4 J5 J6 : Finset (Sym2 V))
    (S : Finset V) : |srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 S| ≤ 14 := by
  unfold srcCert
  simp only [Pi.add_apply]
  have hm := abs_mvec_le (G := G) (lab := lab) (F := F) u v a c b1 J1 J2 S
  have h1 : |(if x1 G lab F u v a J1 = b2 then 0 else
      tvec G lab F J3 J4 u a (x1 G lab F u v a J1) c1 b2) S| ≤ 4 := by
    split_ifs
    · simp
    · exact abs_tvec_le _ _ _ _ _ _ _ _
  have h2 : |(if x2 G lab F u v a J1 = b3 then 0 else
      tvec G lab F J5 J6 v a (x2 G lab F u v a J1) c2 b3) S| ≤ 4 := by
    split_ifs
    · simp
    · exact abs_tvec_le _ _ _ _ _ _ _ _
  calc _ ≤ |mvec G lab F u v a c b1 J1 J2 S| + |(if x1 G lab F u v a J1 = b2 then 0 else
      tvec G lab F J3 J4 u a (x1 G lab F u v a J1) c1 b2) S| +
      |(if x2 G lab F u v a J1 = b3 then 0 else
      tvec G lab F J5 J6 v a (x2 G lab F u v a J1) c2 b3) S| := abs_add_three _ _ _
    _ ≤ 14 := by linarith

/-- The certificate is supported on permitted triangles (for every choice). -/
lemma srcCert_supp {u v a b1 b2 b3 c c1 c2 : V} {J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)}
    {S : Finset V} (h : srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 S ≠ 0) :
    IsAllowed G lab F S := by
  obtain ⟨X, -, hX⟩ := srcCert_ne_zero h
  exact allowed_of_mem_decOf hX

omit [Fintype V] in
lemma support_union_wedge [Fintype V] (J : Finset (Sym2 V)) (p q y : V) :
    support (J ∪ wedge p q y) ⊆ support J ∪ {p, q, y} := by
  intro x hx
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  obtain ⟨e, he, hxe⟩ := hx
  rcases he with he | he
  · exact Or.inl ⟨e, he, hxe⟩
  · right
    simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp only [Sym2.mem_iff] at hxe <;>
      rcases hxe with rfl | rfl <;> simp

/-- **Vertices of the certificate** (for every choice): every vertex of a support triangle
is in `T` or in a set `Ax` containing all revealed vertices. -/
lemma srcCert_verts {u v a b1 b2 b3 c c1 c2 : V} {J1 J2 J3 J4 J5 J6 : Finset (Sym2 V)}
    {S : Finset V} (Ax : Finset V)
    (hJ : ∀ J ∈ [J1, J2, J3, J4, J5, J6], support J ⊆ Ax)
    (hpts : ∀ y ∈ [b1, b2, b3, c, c1, c2], y ∈ ({u, v, a} : Finset V) ∪ Ax)
    (h : srcCert G lab F u v a b1 b2 b3 c c1 c2 J1 J2 J3 J4 J5 J6 S ≠ 0) :
    S ⊆ {u, v, a} ∪ Ax := by
  obtain ⟨X, hXm, hX⟩ := srcCert_ne_zero h
  have hS := subset_support_of_mem_decOf hX
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hJ hpts
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hJ
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpts
  set TA := ({u, v, a} : Finset V) ∪ Ax
  have hT : ∀ y ∈ ({u, v, a} : Finset V), y ∈ TA := fun y hy => Finset.mem_union_left _ hy
  have hu : u ∈ TA := hT u (by simp)
  have hv : v ∈ TA := hT v (by simp)
  have ha : a ∈ TA := hT a (by simp)
  -- a fixed mode of `J ∪ wedge p q y` lies in `TA`
  have key : ∀ (J : Finset (Sym2 V)) (p q y : V), support J ⊆ Ax → p ∈ TA → q ∈ TA →
      y ∈ TA → support (J ∪ wedge p q y) ⊆ TA := by
    intro J p q y hJ hp hq hy x hx
    rcases Finset.mem_union.1 (support_union_wedge J p q y hx) with h1 | h1
    · exact Finset.mem_union_right _ (hJ h1)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl | rfl <;> assumption
  -- the third vertices
  have hQ1 : Q1 G lab F u v a J1 ⊆ TA := by
    rw [Q1_eq]
    rcases cover_subset (decOf G lab F (J1 ∪ wedge u v a)) s(u, a) with h1 | h1
    · exact (subset_support_of_mem_decOf h1).trans (key J1 u v a s1 hu hv ha)
    · rw [h1]; exact Finset.empty_subset _
  have hQ2 : Q2 G lab F u v a J1 ⊆ TA := by
    rw [Q2_eq]
    rcases cover_subset (decOf G lab F (J1 ∪ wedge u v a)) s(v, a) with h1 | h1
    · exact (subset_support_of_mem_decOf h1).trans (key J1 u v a s1 hu hv ha)
    · rw [h1]; exact Finset.empty_subset _
  have hx1 : x1 G lab F u v a J1 ∈ TA := by
    rw [x1_eq]
    rcases third_mem_or (Q1 G lab F u v a J1) u a with h1 | h1
    · exact hQ1 h1
    · rw [h1]; exact hu
  have hx2 : x2 G lab F u v a J1 ∈ TA := by
    rw [x2_eq]
    rcases third_mem_or (Q2 G lab F u v a J1) v a with h1 | h1
    · exact hQ2 h1
    · rw [h1]; exact hv
  refine hS.trans ?_
  simp only [certSets, List.mem_cons, List.not_mem_nil, or_false] at hXm
  rcases hXm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ _ _ _ s1 hu hv ha
  · exact key _ _ _ _ s1 hu hv p4
  · exact key _ _ _ _ s2 hu hv p4
  · exact key _ _ _ _ s2 hu hv p1
  · exact key _ _ _ _ s3 hu ha hx1
  · exact key _ _ _ _ s3 hu ha p5
  · exact key _ _ _ _ s4 hu ha p5
  · exact key _ _ _ _ s4 hu ha p2
  · exact key _ _ _ _ s5 hv ha hx2
  · exact key _ _ _ _ s5 hv ha p6
  · exact key _ _ _ _ s6 hv ha p6
  · exact key _ _ _ _ s6 hv ha p3

end S10V23
