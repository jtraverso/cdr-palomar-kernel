/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.OddSubdivision

@[expose] public section

/-!
# Greedy construction of an odd subdivision from robust short odd paths

Input: a host (link) graph `H`, a relation `Allowed` on host vertices, and the
**robust short odd path condition** `RobustOddPaths H Allowed ℓ B`: for every forbidden set
`Z` with `|Z| ≤ B` and every allowed pair `a, b ∉ Z` there is a path (`Walk.IsPath`) of odd
length `≤ ℓ` from `a` to `b` whose support avoids `Z`.

* `exists_placement` : prescribed injective ports `ψ` are kept; each auxiliary `x` is placed in
  its candidate set `Cand x`, avoiding `Z0` and all earlier images.  Resource:
  `|Z0| + |α| ≤ |Cand x|`.
* `exists_routing` : edges are routed one after another; for the current edge the forbidden
  set is `Z0 ∪ (φ(α) \ {ends}) ∪ (all internals so far)`, of size
  `≤ |Z0| + |α| + (ℓ - 1) e(Q)`.  Resource: `|Z0| + |α| + (ℓ - 1) e(Q) ≤ B`.
* `greedy_embedding` : both together; the output is an actual `OddSubdivision H Q` (data),
  with ports fixed, auxiliaries in their candidate sets, every path length `≤ ℓ`, and
  everything outside `Z0`.  It is chosen with no reference to any mode.
-/

namespace SelEmbed

open Finset SelSubdiv

variable {α V : Type*} [DecidableEq α] [DecidableEq V]

/-- The robust short odd path condition of a host graph for allowed pairs. -/
def RobustOddPaths (H : SimpleGraph V) (Allowed : V → V → Prop) (ℓ B : ℕ) : Prop :=
  ∀ Z : Finset V, Z.card ≤ B → ∀ a b, Allowed a b → a ∉ Z → b ∉ Z →
    ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ ℓ ∧ ∀ z ∈ w.support, z ∉ Z

/-! ### Greedy placement of auxiliaries -/

/-- **Greedy placement.**  Prescribed ports are preserved; auxiliaries are placed injectively
in their candidate sets, avoiding `Z0`. -/
theorem exists_placement [Fintype α] (Ports : Finset α) (ψ : α → V) (hψ : Set.InjOn ψ Ports)
    (Z0 : Finset V) (hψZ : ∀ x ∈ Ports, ψ x ∉ Z0) (Cand : α → Finset V)
    (hCand : ∀ x ∉ Ports, Z0.card + Fintype.card α ≤ (Cand x).card) :
    ∃ φ : α → V, Function.Injective φ ∧ (∀ x ∈ Ports, φ x = ψ x) ∧
      (∀ x ∉ Ports, φ x ∈ Cand x) ∧ ∀ x, φ x ∉ Z0 := by
  have key : ∀ X : Finset α, Disjoint X Ports → ∃ φ : α → V, Set.InjOn φ ↑(Ports ∪ X) ∧
      (∀ x ∈ Ports, φ x = ψ x) ∧ (∀ x ∈ X, φ x ∈ Cand x) ∧ ∀ x ∈ Ports ∪ X, φ x ∉ Z0 := by
    intro X
    induction X using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨ψ, by simpa using hψ, fun _ _ => rfl, by simp, by simpa using hψZ⟩
    | insert a X haX ih =>
      intro hdisj
      have haP : a ∉ Ports := disjoint_left.mp hdisj (mem_insert_self a X)
      obtain ⟨φ, hinj, hP, hC, hZ⟩ := ih (disjoint_of_subset_left (subset_insert a X) hdisj)
      have hlt : (Ports ∪ X).card < Fintype.card α := by
        apply card_lt_univ_of_notMem (x := a)
        simp [haP, haX]
      have hUsed : (Z0 ∪ (Ports ∪ X).image φ).card < (Cand a).card := by
        calc (Z0 ∪ (Ports ∪ X).image φ).card ≤ Z0.card + ((Ports ∪ X).image φ).card :=
              card_union_le _ _
          _ ≤ Z0.card + (Ports ∪ X).card := by gcongr; exact card_image_le
          _ < Z0.card + Fintype.card α := by omega
          _ ≤ _ := hCand a haP
      obtain ⟨c, hc⟩ : (Cand a \ (Z0 ∪ (Ports ∪ X).image φ)).Nonempty := by
        rw [← card_pos]
        have := le_card_sdiff (Z0 ∪ (Ports ∪ X).image φ) (Cand a)
        omega
      rw [mem_sdiff, mem_union, not_or] at hc
      obtain ⟨hcC, hcZ, hcI⟩ := hc
      have hold : ∀ x ∈ Ports ∪ X, x ≠ a := by
        intro x hx hxa; subst hxa; simp [haP, haX] at hx
      refine ⟨Function.update φ a c, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [coe_union, coe_insert, Set.mem_union, Set.mem_insert_iff, mem_coe] at hx hy
        by_cases hxa : x = a <;> by_cases hya : y = a
        · rw [hxa, hya]
        · subst hxa
          have hy' : y ∈ Ports ∪ X := by
            rcases hy with h | h | h
            · exact mem_union_left _ h
            · exact absurd h hya
            · exact mem_union_right _ h
          rw [Function.update_self, Function.update_of_ne hya] at hxy
          exact absurd (hxy ▸ mem_image_of_mem φ hy') hcI
        · subst hya
          have hx' : x ∈ Ports ∪ X := by
            rcases hx with h | h | h
            · exact mem_union_left _ h
            · exact absurd h hxa
            · exact mem_union_right _ h
          rw [Function.update_self, Function.update_of_ne hxa] at hxy
          exact absurd (hxy ▸ mem_image_of_mem φ hx') hcI
        · rw [Function.update_of_ne hxa, Function.update_of_ne hya] at hxy
          have hx' : x ∈ Ports ∪ X := by
            rcases hx with h | h | h
            · exact mem_union_left _ h
            · exact absurd h hxa
            · exact mem_union_right _ h
          have hy' : y ∈ Ports ∪ X := by
            rcases hy with h | h | h
            · exact mem_union_left _ h
            · exact absurd h hya
            · exact mem_union_right _ h
          exact hinj (by exact_mod_cast hx') (by exact_mod_cast hy') hxy
      · intro x hx
        rw [Function.update_of_ne (hold x (mem_union_left _ hx))]
        exact hP x hx
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · rw [Function.update_self]; exact hcC
        · rw [Function.update_of_ne (hold x (mem_union_right _ hx))]; exact hC x hx
      · intro x hx
        by_cases hxa : x = a
        · subst hxa; rw [Function.update_self]; exact hcZ
        · rw [Function.update_of_ne hxa]
          apply hZ
          rcases mem_union.mp hx with h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ ((mem_insert.mp h).resolve_left hxa)
  obtain ⟨φ, hinj, hP, hC, hZ⟩ := key (univ \ Ports) disjoint_sdiff_self_left
  have hall : ∀ x, x ∈ Ports ∪ (univ \ Ports) := fun x => by
    by_cases h : x ∈ Ports
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ x, h⟩)
  refine ⟨φ, fun x y hxy => hinj (by exact_mod_cast hall x) (by exact_mod_cast hall y) hxy,
    hP, fun x hx => hC x (mem_sdiff.mpr ⟨mem_univ x, hx⟩), fun x => hZ x (hall x)⟩

/-! ### Greedy routing of the edges -/

section Routing

variable (H : SimpleGraph V) (φ : α → V) (src tgt : Sym2 α → α) (ℓ : ℕ) (Z0 : Finset V)

/-- A partial routing of the edges `Q'`. -/
structure RouteOK (Q' : Finset (Sym2 α)) (t : Sym2 α → ℕ) (int : Sym2 α → ℕ → V) : Prop where
  inj : ∀ e ∈ Q', ∀ e' ∈ Q', ∀ j j', 1 ≤ j → j ≤ 2 * t e → 1 ≤ j' → j' ≤ 2 * t e' →
    int e j = int e' j' → e = e' ∧ j = j'
  ne : ∀ e ∈ Q', ∀ j, 1 ≤ j → j ≤ 2 * t e → ∀ x, int e j ≠ φ x
  adj : ∀ e ∈ Q', ∀ j, j ≤ 2 * t e →
    H.Adj (pv φ src tgt t int e j) (pv φ src tgt t int e (j + 1))
  len : ∀ e ∈ Q', 2 * t e + 1 ≤ ℓ
  avoid : ∀ e ∈ Q', ∀ j, 1 ≤ j → j ≤ 2 * t e → int e j ∉ Z0

omit [DecidableEq α] [DecidableEq V] in
lemma pv_congr {t t' : Sym2 α → ℕ} {int int' : Sym2 α → ℕ → V} {e : Sym2 α}
    (ht : t' e = t e) (hi : int' e = int e) (j : ℕ) :
    pv φ src tgt t' int' e j = pv φ src tgt t int e j := by
  simp [pv, ht, hi]

variable {H φ src tgt ℓ Z0}

/-- The forbidden set while routing `e`: `Z0`, the other abstract images, and all internal
vertices of the edges already routed. -/
def forbidden [Fintype α] (φ : α → V) (Z0 : Finset V) (Q' : Finset (Sym2 α))
    (t : Sym2 α → ℕ) (int : Sym2 α → ℕ → V) (a b : V) : Finset V :=
  Z0 ∪ ((univ.image φ).erase a).erase b ∪ Q'.biUnion (fun e => (Icc 1 (2 * t e)).image (int e))

omit [DecidableEq α] in
/-- **Forbidden-vertex count**: `|Z| ≤ |Z0| + |α| + (ℓ - 1) |Q'|`. -/
theorem forbidden_card_le [Fintype α] {Q' : Finset (Sym2 α)} {t : Sym2 α → ℕ}
    {int : Sym2 α → ℕ → V} (hlen : ∀ e ∈ Q', 2 * t e + 1 ≤ ℓ) (a b : V) :
    (forbidden φ Z0 Q' t int a b).card ≤ Z0.card + Fintype.card α + (ℓ - 1) * Q'.card := by
  unfold forbidden
  have h1 : (((univ : Finset α).image φ).erase a).erase b ⊆ univ.image φ :=
    (erase_subset _ _).trans (erase_subset _ _)
  have h2 : (Q'.biUnion (fun e => (Icc 1 (2 * t e)).image (int e))).card ≤ (ℓ - 1) * Q'.card := by
    refine card_biUnion_le.trans ?_
    have : ∀ e ∈ Q', ((Icc 1 (2 * t e)).image (int e)).card ≤ ℓ - 1 := by
      intro e he
      refine card_image_le.trans ?_
      rw [Nat.card_Icc]; have := hlen e he; omega
    refine (sum_le_sum this).trans ?_
    rw [sum_const, smul_eq_mul, mul_comm]
  have h3 := card_le_card h1
  have h4 : (univ.image φ).card ≤ Fintype.card α := card_image_le.trans (by simp)
  calc _ ≤ (Z0 ∪ ((univ.image φ).erase a).erase b).card +
        (Q'.biUnion (fun e => (Icc 1 (2 * t e)).image (int e))).card := card_union_le _ _
    _ ≤ Z0.card + (((univ.image φ).erase a).erase b).card + (ℓ - 1) * Q'.card := by
        gcongr; exact card_union_le _ _
    _ ≤ _ := by omega

/-- **One routing step**: a new edge is routed by a robust odd path avoiding the forbidden set. -/
theorem route_step [Fintype α] {Allowed : V → V → Prop} {B : ℕ}
    (hR : RobustOddPaths H Allowed ℓ B) (hφ : Function.Injective φ) (hφZ : ∀ x, φ x ∉ Z0)
    {Q' : Finset (Sym2 α)} {e : Sym2 α} (heQ' : e ∉ Q') {t : Sym2 α → ℕ}
    {int : Sym2 α → ℕ → V} (hok : RouteOK H φ src tgt ℓ Z0 Q' t int)
    (hne : src e ≠ tgt e) (hall : Allowed (φ (src e)) (φ (tgt e)))
    (hB : Z0.card + Fintype.card α + (ℓ - 1) * Q'.card ≤ B) :
    ∃ t' int', RouteOK H φ src tgt ℓ Z0 (insert e Q') t' int' := by
  set a := φ (src e)
  set b := φ (tgt e)
  set Z := forbidden φ Z0 Q' t int a b with hZdef
  have hab : a ≠ b := fun h => hne (hφ h)
  have hints : ∀ e' ∈ Q', ∀ j, 1 ≤ j → j ≤ 2 * t e' → int e' j ∈ Z := by
    intro e' he' j h1 h2
    refine mem_union_right _ (mem_biUnion.mpr ⟨e', he', mem_image.mpr ⟨j, ?_, rfl⟩⟩)
    rw [mem_Icc]; exact ⟨h1, h2⟩
  have himg : ∀ x, φ x ≠ a → φ x ≠ b → φ x ∈ Z := by
    intro x ha hb
    refine mem_union_left _ (mem_union_right _ ?_)
    rw [mem_erase, mem_erase]
    exact ⟨hb, ha, mem_image_of_mem _ (mem_univ x)⟩
  have hZ0 : Z0 ⊆ Z := fun z hz => mem_union_left _ (mem_union_left _ hz)
  have haZ : a ∉ Z := by
    simp only [hZdef, forbidden, mem_union, mem_erase, mem_biUnion, mem_image, not_or]
    refine ⟨⟨hφZ _, by tauto⟩, ?_⟩
    rintro ⟨e', he', j, hj, hj'⟩
    rw [mem_Icc] at hj
    exact hok.ne e' he' j hj.1 hj.2 _ hj'
  have hbZ : b ∉ Z := by
    simp only [hZdef, forbidden, mem_union, mem_erase, mem_biUnion, mem_image, not_or]
    refine ⟨⟨hφZ _, by tauto⟩, ?_⟩
    rintro ⟨e', he', j, hj, hj'⟩
    rw [mem_Icc] at hj
    exact hok.ne e' he' j hj.1 hj.2 _ hj'
  obtain ⟨w, hpath, hodd, hlen, hsupp⟩ :=
    hR Z ((forbidden_card_le hok.len a b).trans hB) a b hall haZ hbZ
  obtain ⟨t0, ht0⟩ := hodd
  have hwZ : ∀ i, w.getVert i ∉ Z := fun i => hsupp _ (w.getVert_mem_support i)
  have hwinj : ∀ i i', i ≤ w.length → i' ≤ w.length → w.getVert i = w.getVert i' → i = i' :=
    fun i i' hi hi' h => hpath.getVert_injOn hi hi' h
  refine ⟨Function.update t e t0, Function.update int e (fun j => w.getVert j), ?_⟩
  have hte : Function.update t e t0 e = t0 := Function.update_self ..
  have hie : Function.update int e (fun j => w.getVert j) e = fun j => w.getVert j :=
    Function.update_self ..
  have hto : ∀ e' ∈ Q', Function.update t e t0 e' = t e' := fun e' he' =>
    Function.update_of_ne (fun h => heQ' (by rw [← h]; exact he')) _ _
  have hio : ∀ e' ∈ Q', Function.update int e (fun j => w.getVert j) e' = int e' :=
    fun e' he' => Function.update_of_ne (fun h => heQ' (by rw [← h]; exact he')) _ _
  have hpv : ∀ j, j ≤ 2 * t0 + 1 →
      pv φ src tgt (Function.update t e t0) (Function.update int e (fun j => w.getVert j)) e j =
        w.getVert j := by
    intro j hj
    simp only [pv, hte, hie]
    split_ifs with h0 h1
    · subst h0; rw [SimpleGraph.Walk.getVert_zero]
    · subst h1; rw [← ht0, SimpleGraph.Walk.getVert_length]
    · rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e1 he1 e2 he2 j j' h1 h2 h1' h2' h
    rcases mem_insert.mp he1 with h1e | he1 <;> rcases mem_insert.mp he2 with h2e | he2
    · rw [h1e] at h2 h ⊢; rw [h2e] at h2' h ⊢
      rw [hte] at h2 h2'
      rw [hie] at h
      exact ⟨rfl, hwinj j j' (by omega) (by omega) h⟩
    · rw [h1e] at h2 h; rw [hte] at h2; rw [hto e2 he2] at h2'
      rw [hie, hio e2 he2] at h
      beta_reduce at h
      exact absurd (h ▸ hints e2 he2 j' h1' h2') (hwZ j)
    · rw [h2e] at h2' h; rw [hto e1 he1] at h2; rw [hte] at h2'
      rw [hie, hio e1 he1] at h
      beta_reduce at h
      exact absurd (h ▸ hints e1 he1 j h1 h2) (hwZ j')
    · rw [hto e1 he1] at h2; rw [hto e2 he2] at h2'
      rw [hio e1 he1, hio e2 he2] at h
      exact hok.inj e1 he1 e2 he2 j j' h1 h2 h1' h2' h
  · intro e1 he1 j h1 h2 x
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte] at h2
      rw [hie]
      intro h
      beta_reduce at h
      by_cases hxa : φ x = a
      · rw [hxa] at h
        have := hwinj j 0 (by omega) (by omega) (h.trans (SimpleGraph.Walk.getVert_zero w).symm)
        omega
      by_cases hxb : φ x = b
      · rw [hxb] at h
        have := hwinj j _ (by omega) le_rfl (h.trans (SimpleGraph.Walk.getVert_length w).symm)
        omega
      exact hwZ j (h ▸ himg x hxa hxb)
    · rw [hto e1 he1] at h2; rw [hio e1 he1]
      exact hok.ne e1 he1 j h1 h2 x
  · intro e1 he1 j hj
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte] at hj
      rw [hpv j (by omega), hpv (j + 1) (by omega)]
      exact w.adj_getVert_succ (by omega)
    · rw [hto e1 he1] at hj
      rw [pv_congr φ src tgt (hto e1 he1) (hio e1 he1),
        pv_congr φ src tgt (hto e1 he1) (hio e1 he1)]
      exact hok.adj e1 he1 j hj
  · intro e1 he1
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hte]; omega
    · rw [hto e1 he1]; exact hok.len e1 he1
  · intro e1 he1 j h1 h2
    rcases mem_insert.mp he1 with rfl | he1
    · rw [hie]; exact fun h => hwZ j (hZ0 h)
    · rw [hto e1 he1] at h2; rw [hio e1 he1]
      exact hok.avoid e1 he1 j h1 h2

/-- **Greedy routing of all edges of `Q`.** -/
theorem exists_routing [Fintype α] {Allowed : V → V → Prop} {B : ℕ}
    (hR : RobustOddPaths H Allowed ℓ B) (hφ : Function.Injective φ) (hφZ : ∀ x, φ x ∉ Z0)
    (Q : Finset (Sym2 α)) (hne : ∀ e ∈ Q, src e ≠ tgt e)
    (hall : ∀ e ∈ Q, Allowed (φ (src e)) (φ (tgt e)))
    (hB : Z0.card + Fintype.card α + (ℓ - 1) * Q.card ≤ B) :
    ∃ t int, RouteOK H φ src tgt ℓ Z0 Q t int := by
  have key : ∀ Q' : Finset (Sym2 α), Q' ⊆ Q → ∃ t int, RouteOK H φ src tgt ℓ Z0 Q' t int := by
    intro Q'
    induction Q' using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => 0, fun e _ => φ (src e), by simp, by simp, by simp, by simp, by simp⟩
    | insert e Q' heQ' ih =>
      intro hsub
      obtain ⟨t, int, hok⟩ := ih ((subset_insert e Q').trans hsub)
      have heQ : e ∈ Q := hsub (mem_insert_self e Q')
      have hcard : Q'.card ≤ Q.card := card_le_card ((subset_insert e Q').trans hsub)
      exact route_step hR hφ hφZ heQ' hok (hne e heQ) (hall e heQ)
        (le_trans (by gcongr) hB)
  exact key Q subset_rfl

end Routing

/-! ### The greedy embedding -/

/-- **Greedy odd-subdivision embedding.**  From the robust short odd path condition, prescribed
injective ports `ψ` (on `Ports`, outside `Z0`), candidate sets for auxiliaries, a side
predicate making every abstract edge an allowed pair, and the explicit resource inequalities,
an actual odd subdivision of `Q` in `H` is constructed (data, chosen before any mode). -/
theorem greedy_embedding [Fintype α] (H : SimpleGraph V) (Allowed : V → V → Prop) {ℓ B : ℕ}
    (hR : RobustOddPaths H Allowed ℓ B) (Q : Finset (Sym2 α)) (hQ : ∀ e ∈ Q, ¬ e.IsDiag)
    (Side : α → V → Prop)
    (hside : ∀ e ∈ Q, ∀ x y, s(x, y) = e → ∀ a b, a ≠ b → Side x a → Side y b → Allowed a b)
    (Ports : Finset α) (ψ : α → V) (hψ : Set.InjOn ψ Ports) (hψS : ∀ x ∈ Ports, Side x (ψ x))
    (Z0 : Finset V) (hψZ : ∀ x ∈ Ports, ψ x ∉ Z0)
    (Cand : α → Finset V) (hCS : ∀ x ∉ Ports, ∀ a ∈ Cand x, Side x a)
    (hCand : ∀ x ∉ Ports, Z0.card + Fintype.card α ≤ (Cand x).card)
    (hB : Z0.card + Fintype.card α + (ℓ - 1) * Q.card ≤ B) :
    ∃ D : OddSubdivision H Q, (∀ x ∈ Ports, D.φ x = ψ x) ∧ (∀ x ∉ Ports, D.φ x ∈ Cand x) ∧
      (∀ x, D.φ x ∉ Z0) ∧ (∀ e ∈ Q, 2 * D.t e + 1 ≤ ℓ) ∧ (∀ y ∈ D.internals, y ∉ Z0) := by
  obtain ⟨φ, hφ, hP, hC, hZ⟩ := exists_placement Ports ψ hψ Z0 hψZ Cand hCand
  have hSide : ∀ x, Side x (φ x) := by
    intro x
    by_cases hx : x ∈ Ports
    · rw [hP x hx]; exact hψS x hx
    · exact hCS x hx _ (hC x hx)
  let src : Sym2 α → α := fun e => e.out.1
  let tgt : Sym2 α → α := fun e => e.out.2
  have hends : ∀ e, s(src e, tgt e) = e := fun e => by
    change Quot.mk _ e.out = e
    exact e.out_eq
  have hne : ∀ e ∈ Q, src e ≠ tgt e := by
    intro e he h
    apply hQ e he
    rw [← hends e, h]
    exact Sym2.mk_isDiag_iff.mpr rfl
  have hall : ∀ e ∈ Q, Allowed (φ (src e)) (φ (tgt e)) := fun e he =>
    hside e he _ _ (hends e) _ _ (fun h => hne e he (hφ h)) (hSide _) (hSide _)
  obtain ⟨t, int, hok⟩ := exists_routing (H := H) (src := src) (tgt := tgt) hR hφ hZ Q hne hall hB
  refine ⟨⟨φ, src, tgt, t, int, hφ, fun e _ => hends e, hne, hok.inj, hok.ne, hok.adj⟩,
    hP, hC, hZ, hok.len, ?_⟩
  intro y hy
  obtain ⟨e, he, j, h1, h2, rfl⟩ := (OddSubdivision.mem_internals _).mp hy
  exact hok.avoid e he j h1 h2

end SelEmbed
