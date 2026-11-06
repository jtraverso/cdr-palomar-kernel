/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V36.NativeGauge
public import RequestProject.TypedTriangle.ComponentRowsConverse
public import RequestProject.TypedTriangle.LocalProfileModule
public import RequestProject.S07V38.BoundedExtension
@[expose] public section

/-!
# V38 §2 — the actual real annihilator of the native local-profile module

Host `(G, lab, F)` as in the original contract; native matrix `natB` of V36 (rows: active
bipartite link components `NRow`; columns: host edges in an allowed triangle `NCol`).
"Local profile" is the existing `IsLocalProfile G lab F` (carrier of `localProfile`), i.e.
the LOCAL module `M`; nothing here is about the physical triangle lattice `Λ`.

* `localProfile_supp` — every local profile vanishes off the native columns;
* `natB_row_star` — on vectors supported on native columns, row `(v, K)` of `natB` is the
  signed star `∑_{u ∈ K} sgn(col u) x(vu)`;
* `localProfile_natB` — **every actual local profile is annihilated by `natB`** (not only
  triangle certificates);
* `two_mul_isLocalProfile` — **if `x` is an integer vector supported on the native columns
  with `natB x = 0`, then `2x` is an actual local profile.** Proof through the existing integer
  image characterisation of unoriented incidence (`kernel_isLocalProfile`, i.e.
  `restrict_mem_starIm`): bipartite components by exact balance (from `natB x = 0` on
  active components, trivially on isolated ones), non-bipartite components by doubling;
* `realKer` — the real kernel of `natB` on vectors supported on the native columns;
* `span_localProfile_eq` — **`span_ℝ (local profiles) = ker_ℝ natB`**; the rational-to-real
  step is `realKer_mem_span` applied to an INTEGER matrix (`fullB`: the rows of `natB` and the
  support equations);
* `rowSpan_of_annihilates` — **a real functional on the native columns that vanishes on every
  local profile is `natBᵀ t` for an actual row potential `t`.**

No identification of `ker natB` with the physical lattice (or its saturation) is made.
-/

open Finset Classical

noncomputable section

namespace S07V38

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
  TypedTriangle.SignedCover S07V36 S10V22

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-! ### Elementary facts on native columns -/

omit [Fintype V] in
lemma ncol_linkActive {v u : V} (h : IsNCol G lab F s(v, u)) : LinkActive G lab F v u := by
  obtain ⟨T, hT, he⟩ := h
  obtain ⟨hv, hu, hvu⟩ := mem_triEdges.1 he
  obtain ⟨w, -, hwu, rfl⟩ := allowed_eq_triple hT.1 hv hu hvu
  exact ⟨w, hwu.symm, hT⟩

lemma ncol_mem_edges {e : Sym2 V} (h : IsNCol G lab F e) : e ∈ edges G := by
  obtain ⟨T, hT, he⟩ := h
  exact TypedTriangle.Composition.mem_edges_of_mem_triEdges G lab F hT he

lemma mem_comp_self' (v u : V) : u ∈ comp G lab F v u := by simp [comp]

/-- **Local profiles live on the native columns.** -/
theorem localProfile_supp {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) (e : Sym2 V)
    (he : ¬ IsNCol G lab F e) : x e = 0 := by
  induction e using Sym2.ind with
  | h a b =>
    by_cases hab : a = b
    · subst hab
      exact hx.1 _ (by rw [mem_edges, SimpleGraph.mem_edgeSet]; exact G.irrefl)
    · obtain ⟨c, hc⟩ := hx.2 a
      rw [hc b (Ne.symm hab)]
      refine Finset.sum_eq_zero fun T hT => absurd ?_ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact ⟨T, hT.1.1, mem_triEdges.2 ⟨hT.1.2, hT.2, hab⟩⟩

/-- Sums over native columns as filtered sums over all pairs. -/
lemma sum_ncol {R : Type*} [AddCommMonoid R] (f : Sym2 V → R) :
    ∑ e : NCol G lab F, f e.1 = ∑ e, if IsNCol G lab F e then f e else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

omit [Fintype V] in
/-- An entry as a sum over the other endpoint. -/
lemma entry_eq_sum [Fintype V] (j : Row V) (e : Sym2 V) :
    entry G lab F j e = ∑ u, if e = s(j.1, u) then
      (if u ∈ j.2 then sgn (TypedTriangle.ComponentRows.col G lab F j u) else 0) else 0 := by
  by_cases h : j.1 ∈ e
  · have he : e = s(j.1, Sym2.Mem.other h) := (Sym2.other_spec h).symm
    rw [Finset.sum_eq_single (Sym2.Mem.other h)]
    · rw [if_pos he]; unfold entry; rw [dif_pos h]
    · intro u _ hu
      rw [if_neg]
      intro h'
      rw [he] at h'
      exact hu (Sym2.congr_right.1 h').symm
    · simp
  · rw [entry_of_not_mem h]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg]
    rintro rfl
    exact h (Sym2.mem_mk_left _ _)

/-- **Row of `natB` = signed star**, for vectors supported on the native columns. -/
theorem natB_row_star {R : Type*} [CommRing R] (j : NRow G lab F) (x : Sym2 V → R)
    (hx : ∀ e, ¬ IsNCol G lab F e → x e = 0) :
    ∑ e : NCol G lab F, (natB G lab F j e : R) * x e.1 =
      ∑ u, if u ∈ j.1.2 then
        (sgn (TypedTriangle.ComponentRows.col G lab F j.1 u) : R) * x s(j.1.1, u) else 0 := by
  show ∑ e : NCol G lab F, (entry G lab F j.1 e.1 : R) * x e.1 = _
  rw [sum_ncol (fun e => (entry G lab F j.1 e : R) * x e)]
  rw [Finset.sum_congr rfl (fun e _ => show (if IsNCol G lab F e then
      (entry G lab F j.1 e : R) * x e else 0) = (entry G lab F j.1 e : R) * x e from by
    split_ifs with h
    · rfl
    · rw [hx e h, mul_zero])]
  simp_rw [entry_eq_sum, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single s(j.1.1, u)]
  · simp only [if_true]
    split_ifs <;> simp
  · intro e _ he
    simp [he]
  · simp

/-- On a native row, the component condition is membership and the sign is the colour. -/
lemma star_bridge {R : Type*} [CommRing R] (j : NRow G lab F) (x : Sym2 V → R) :
    (∑ u, if comp G lab F j.1.1 u = j.1.2 then
      (sgn (sigma G lab F (j.1.1, j.1.2) u) : R) * x s(j.1.1, u) else 0) =
    ∑ u, if u ∈ j.1.2 then
      (sgn (TypedTriangle.ComponentRows.col G lab F j.1 u) : R) * x s(j.1.1, u) else 0 := by
  refine Finset.sum_congr rfl fun u _ => ?_
  have hiff : comp G lab F j.1.1 u = j.1.2 ↔ u ∈ j.1.2 :=
    ⟨fun h => h ▸ mem_comp_self' _ _, fun h => (active_eq_comp j.2.1 h).symm⟩
  have hsig : sigma G lab F (j.1.1, j.1.2) u = TypedTriangle.ComponentRows.col G lab F j.1 u := by
    unfold sigma; rw [if_pos j.2.2]
  simp only [hiff, hsig]

/-! ### Forward: local profiles are annihilated -/

/-- **Every actual local profile is annihilated by the native matrix.** -/
theorem localProfile_natB {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) (j : NRow G lab F) :
    ∑ e : NCol G lab F, natB G lab F j e * x e.1 = 0 := by
  have h := natB_row_star (R := ℤ) j x (localProfile_supp hx)
  have h2 := star_bridge (R := ℤ) j x
  simp only [Int.cast_id] at h h2
  rw [h, ← h2]
  obtain ⟨c, hc⟩ := hx.2 j.1.1
  rw [star_eq_sum_tri G lab F x hx.1 j.1.1 j.1.2 c (fun w hw => hc w hw)]
  exact Finset.sum_eq_zero fun T hT => by rw [(triVal_spec G lab F _ _ hT).1 j.2.2, mul_zero]

/-! ### Converse up to doubling -/

/-- **Doubling converse.** An integer vector supported on the native columns with `natB x = 0`
becomes an actual local profile after doubling. -/
theorem two_mul_isLocalProfile (x : Sym2 V → ℤ) (hs : ∀ e, ¬ IsNCol G lab F e → x e = 0)
    (hk : ∀ j : NRow G lab F, ∑ e : NCol G lab F, natB G lab F j e * x e.1 = 0) :
    IsLocalProfile G lab F (fun e => 2 * x e) := by
  have hsE : ∀ e, e ∉ edges G → x e = 0 := fun e he => hs e (fun h => he (ncol_mem_edges h))
  -- balance of every bipartite row
  have hbal : ∀ j : Row V, IsBip G lab F j →
      ∑ u, (if comp G lab F j.1 u = j.2 then sgn (sigma G lab F j u) * x s(j.1, u) else 0) =
        0 := by
    intro j hb
    by_cases hact : IsActiveRow G lab F j
    · have h1 := hk ⟨j, hact, hb⟩
      have h3 := natB_row_star (R := ℤ) ⟨j, hact, hb⟩ x hs
      have h2 := star_bridge (R := ℤ) ⟨j, hact, hb⟩ x
      simp only [Int.cast_id] at h3 h2
      rw [h3] at h1
      exact h2.trans h1
    · refine Finset.sum_eq_zero fun u _ => ?_
      split_ifs with h
      · rw [hs s(j.1, u) (fun hn => hact ⟨u, ncol_linkActive hn, h⟩), mul_zero]
      · rfl
  set y : Col G → ℤ := fun e => 2 * x e.1 with hy
  set w : Row V → ℤ := fun j => if IsBip G lab F j then 0 else ∑ e : Col G, term G lab F x e j
    with hw
  have hterm : ∀ e j, term G lab F (fun e => 2 * x e) e j = 2 * term G lab F x e j := by
    intro e j; unfold term; split_ifs <;> ring
  have hker : ∀ j, baug (rowSys G lab F) y w j = 0 := by
    intro j
    rw [hy, baug_rowSys G lab F (fun e => 2 * x e) w j]
    simp only [hterm, ← Finset.mul_sum]
    by_cases hb : IsBip G lab F j
    · simp only [hw, if_pos hb]
      rw [sum_term_eq G lab F x hsE j, hbal j hb]
      ring
    · simp only [hw, if_neg hb]
      ring
  have hL := kernel_isLocalProfile G lab F y w (fun j hj => by simp [hw, hj]) hker
  have hext : extE G y = fun e => 2 * x e := by
    funext e
    unfold extE
    split_ifs with h
    · rfl
    · simp [hsE e (by rw [mem_edges]; exact h)]
  rwa [hext] at hL

/-! ### Real kernel and real span -/

variable (G lab F) in
/-- **Real kernel of the native matrix** on vectors supported on the native columns. -/
def realKer : Submodule ℝ (Sym2 V → ℝ) where
  carrier := {x | (∀ e, ¬ IsNCol G lab F e → x e = 0) ∧
    ∀ j : NRow G lab F, ∑ e : NCol G lab F, (natB G lab F j e : ℝ) * x e.1 = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun e he => by simp [hx1 e he, hy1 e he], fun j => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx2 j, hy2 j, add_zero]
  zero_mem' := ⟨fun _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨fun e he => by simp [hx1 e he], fun j => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ e : NCol G lab F, (natB G lab F j e : ℝ) * (c * x e.1) =
      c * ∑ e : NCol G lab F, (natB G lab F j e : ℝ) * x e.1 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring, hx2 j, mul_zero]

lemma mem_realKer {x : Sym2 V → ℝ} : x ∈ realKer G lab F ↔ (∀ e, ¬ IsNCol G lab F e → x e = 0) ∧
    ∀ j : NRow G lab F, ∑ e : NCol G lab F, (natB G lab F j e : ℝ) * x e.1 = 0 := Iff.rfl

theorem castV_mem_realKer {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x) :
    castV x ∈ realKer G lab F := by
  refine ⟨fun e he => by simp [castV, localProfile_supp hx e he], fun j => ?_⟩
  have := localProfile_natB hx j
  simp only [castV]
  exact_mod_cast this

variable (G lab F) in
/-- The integer matrix used for the rational-to-real step: the rows of `natB` (extended by
zero to all pairs) and the support equations `x e = 0` for non-native `e`. -/
def fullB : (NRow G lab F ⊕ Sym2 V) → Sym2 V → ℤ
  | Sum.inl j, e => if IsNCol G lab F e then entry G lab F j.1 e else 0
  | Sum.inr e', e => if e = e' ∧ ¬ IsNCol G lab F e' then 1 else 0

lemma fullB_inr_sum {R : Type*} [CommRing R] (e' : Sym2 V) (x : Sym2 V → R) :
    ∑ e, (fullB G lab F (Sum.inr e') e : R) * x e = if IsNCol G lab F e' then 0 else x e' := by
  simp only [fullB]
  by_cases h : IsNCol G lab F e'
  · simp [h]
  · simp [h]

lemma fullB_inl_sum {R : Type*} [CommRing R] (j : NRow G lab F) (x : Sym2 V → R) :
    ∑ e, (fullB G lab F (Sum.inl j) e : R) * x e =
      ∑ e : NCol G lab F, (natB G lab F j e : R) * x e.1 := by
  show _ = ∑ e : NCol G lab F, (entry G lab F j.1 e.1 : R) * x e.1
  rw [sum_ncol (fun e => (entry G lab F j.1 e : R) * x e)]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [fullB]
  split_ifs <;> simp

/-- **The real span of the actual integer local profiles is the real kernel of `natB`.** -/
theorem span_localProfile_eq :
    Submodule.span ℝ (castV '' {x : Sym2 V → ℤ | IsLocalProfile G lab F x}) =
      realKer G lab F := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact castV_mem_realKer hx
  · intro x hx
    have hspan := realKer_mem_span (fullB G lab F) x (fun r => by
      rcases r with j | e'
      · rw [fullB_inl_sum]; exact hx.2 j
      · rw [fullB_inr_sum]
        split_ifs with h
        · rfl
        · exact hx.1 e' h)
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨z, hz, rfl⟩
    have hzs : ∀ e, ¬ IsNCol G lab F e → z e = 0 := fun e he => by
      have := hz (Sum.inr e)
      have h' := fullB_inr_sum (R := ℤ) (G := G) (lab := lab) (F := F) e z
      simp only [Int.cast_id] at h'
      rw [h'] at this
      simpa [he] using this
    have hzk : ∀ j : NRow G lab F, ∑ e : NCol G lab F, natB G lab F j e * z e.1 = 0 :=
      fun j => by
        have := hz (Sum.inl j)
        have h' := fullB_inl_sum (R := ℤ) j z
        simp only [Int.cast_id] at h'
        rw [h'] at this
        simpa using this
    have h2 := two_mul_isLocalProfile z hzs hzk
    have : castV z = (1 / 2 : ℝ) • castV (fun e => 2 * z e) := by
      funext e
      simp only [castV, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2, rfl⟩)

/-! ### Dual statement: row potentials -/

/-- **Row-span characterisation.** A real functional `λ` on the native columns vanishing on
every actual local profile equals `natBᵀ t` on every native column (anchor columns included)
for an actual row potential `t : NRow → ℝ`. -/
theorem rowSpan_of_annihilates (lam : NCol G lab F → ℝ)
    (h : ∀ x : Sym2 V → ℤ, IsLocalProfile G lab F x →
      ∑ e : NCol G lab F, lam e * (x e.1 : ℝ) = 0) :
    ∃ t : NRow G lab F → ℝ, ∀ e, S07V35.dat (natB G lab F) t e = lam e := by
  let f : (NCol G lab F → ℝ) →ₗ[ℝ] (NRow G lab F → ℝ) := realOp (natB G lab F)
  let res : (Sym2 V → ℝ) →ₗ[ℝ] (NCol G lab F → ℝ) := LinearMap.funLeft ℝ ℝ Subtype.val
  have hΛ : Submodule.span ℝ (castV '' {x : Sym2 V → ℤ | IsLocalProfile G lab F x}) ≤
      LinearMap.ker ((valOp lam).comp res) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, valOp_apply, ← h x hx]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp [res, castV, mul_comm]
  have hann : valOp lam ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    let x : Sym2 V → ℝ := fun e => if he : IsNCol G lab F e then y ⟨e, he⟩ else 0
    have hxy : res x = y := by
      funext e
      simp [res, x, e.2]
    have hxK : x ∈ realKer G lab F := by
      refine ⟨fun e he => by simp [x, he], fun j => ?_⟩
      have := congrFun hy j
      simp only [f, realOp_apply, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [x, e.2]
    rw [← span_localProfile_eq] at hxK
    have := hΛ hxK
    rw [LinearMap.mem_ker, LinearMap.comp_apply, hxy] at this
    exact this
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨ψ, hψ⟩ := hann
  refine ⟨fun j => ψ (fun k => if j = k then 1 else 0), fun e => ?_⟩
  have hfe : f (fun i => if e = i then 1 else 0) = fun j => (natB G lab F j e : ℝ) := by
    funext j
    simp [f, realOp_apply]
  have key := LinearMap.congr_fun hψ (fun i => if e = i then (1 : ℝ) else 0)
  rw [LinearMap.dualMap_apply, hfe, valOp_apply] at key
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at key
  rw [← key, LinearMap.pi_apply_eq_sum_univ ψ]
  unfold S07V35.dat
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul]

end S07V38
