/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V45.CoreContract
@[expose] public section

/-!
# V45 §3 — intrinsic local-profile transfer into the core

Under `CorePathContract H lab F W t` (`t` odd, `t ≥ 3`):

* `starIm_core_of_orig` — an integer star vector `f ∈ starIm L_v(H)` (the integer image of the
  unoriented incidence of the ORIGINAL link at `v ∈ W`) that is supported on vertices of `W`
  lies in `starIm L_v(H[W])`. The proof is integral: it uses the explicit transport map
  `rho` that sends `δ_u` to `±δ_{z_C}` (the sign is the original colour relation) and the odd
  routes of the contract; no real span and no saturation is used;
* `mem_MCore_of_contract` — **every integer edge vector supported on `edges(H[W])` and lying in
  the ORIGINAL `localProfile H` belongs to `MCore H lab F W = localProfile (indG H W)`**;
* `mem_MCore_of_lattice` — in particular every ambient-physical (`∈ lattice H lab F`),
  core-supported vector lies in `MCore`.

This is a profile statement only; nothing is claimed about physical-lattice persistence.
-/

open Finset Classical

noncomputable section

namespace S07V45

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.ActiveCover S07V42

variable {V I : Type*} [Fintype V]

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V} {t : ℕ}

/-! ### Triangles at a root -/

omit [Fintype V] in
/-- an allowed triangle through `v` and `u ≠ v` is `{v, u, w}` for a link edge `u w` -/
lemma tri_decomp {T : Finset V} (hT : IsAllowed H lab F T) {v u : V} (hv : v ∈ T) (hu : u ∈ T)
    (huv : u ≠ v) : ∃ w, (link H lab F v).Adj u w ∧ T = {v, u, w} := by
  have h1 : ((T.erase v).erase u).card = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨huv, hu⟩), card_erase_of_mem hv, hT.1]
  obtain ⟨w, hw⟩ := card_eq_one.1 h1
  have hwT : w ∈ (T.erase v).erase u := hw ▸ mem_singleton_self w
  simp only [mem_erase] at hwT
  obtain ⟨hwu, hwv, hwT⟩ := hwT
  have hTeq : T = {v, u, w} := by
    ext a
    simp only [mem_insert, mem_singleton]
    constructor
    · intro ha
      by_cases hav : a = v
      · exact Or.inl hav
      by_cases hau : a = u
      · exact Or.inr (Or.inl hau)
      have : a ∈ (T.erase v).erase u := by simp [hav, hau, ha]
      rw [hw, mem_singleton] at this
      exact Or.inr (Or.inr this)
    · rintro (rfl | rfl | rfl) <;> assumption
  exact ⟨w, ⟨fun h => hwu h.symm, hTeq ▸ hT⟩, hTeq⟩

omit [Fintype V] in
lemma triVec_triple {v u w : V} (huw : u ≠ w) (huv : u ≠ v) (hwv : w ≠ v) :
    triVec v {v, u, w} = dl u + dl w := by
  funext a
  simp only [triVec, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply, dl,
    Pi.single_apply]
  by_cases hau : a = u
  · subst hau; simp [huw, huv]
  · by_cases haw : a = w
    · subst haw; simp [hau, hwv]
    · simp [hau, haw]

/-! ### The transport map -/

variable (H lab F W)

/-- the transport of `δ_u` (for `u` in the original component `K`) to the base `z_K ∈ K ∩ W` -/
def rhoK (v : V) (K : Finset V) (u : V) : V → ℤ :=
  if h : ∃ z, z ∈ K ∧ z ∈ W then
    (if IsBip H lab F (v, K) ∧ col H lab F (v, K) u ≠ col H lab F (v, K) h.choose then -1 else 1)
      • dl h.choose
  else 0

/-- the transport map on unit vectors -/
def rho (v : V) (u : V) : V → ℤ := rhoK H lab F W v (comp H lab F v u) u

variable {H lab F W}

/-- the core image of `2 δ_z` on a NONBIPARTITE original component (odd closed route) -/
theorem two_dl_core (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v)
    (hnb : ¬ IsBip H lab F (v, C)) {z : V} (hz : z ∈ C) (hzW : z ∈ W) :
    (2 : ℤ) • dl z ∈ starIm (indG H W) lab F v := by
  obtain ⟨n, m, hzn, hnm, hmz⟩ := core_nbr hCt ht3 hv hC hz hzW
  have hnC : n ∈ C := mem_of_adj hC hz (link_indG_le v hzn).reachable
  have hmC : m ∈ C := mem_of_adj hC hnC (link_indG_le v hnm).reachable
  have hmW : m ∈ W := (link_indG_adj.1 hnm).2.2.2
  let r : (link (indG H W) lab F v).Walk z m :=
    SimpleGraph.Walk.cons hzn (SimpleGraph.Walk.cons hnm SimpleGraph.Walk.nil)
  have e1 := (walk_starIm _ lab F r).1 (by show Even 2; decide)
  have hadm : OrigAdm H lab F v m z := ⟨C, hC, hmC, hz, hmz, fun h => absurd h hnb⟩
  have e2 := adm_starIm hCt ht hv hadm hmW hzW
  have := Submodule.add_mem _ e1 e2
  have e : dl z - dl m + (dl m + dl z) = (2 : ℤ) • dl z := by rw [two_smul]; abel
  rwa [e] at this

/-- the transport of a link edge lands in the core image -/
theorem rhoK_edge (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {u w : V} (huw : (link H lab F v).Adj u w) :
    rhoK H lab F W v (comp H lab F v u) u + rhoK H lab F W v (comp H lab F v u) w ∈
      starIm (indG H W) lab F v := by
  set K := comp H lab F v u with hK
  have hKa : K ∈ S07V25.activeComps H lab F v := mem_activeComps_of_active huw
  have huK : u ∈ K := self_mem_comp v u
  have hwK : w ∈ K := mem_of_adj hKa huK huw.reachable
  unfold rhoK
  split_ifs with h h1 h2 h2
  · exfalso
    have hc := col_proper h1.1 huK hwK huw
    revert hc h1 h2
    cases col H lab F (v, K) u <;> cases col H lab F (v, K) w <;>
      cases col H lab F (v, K) h.choose <;> simp
  · rw [← add_smul]; simp
  · rw [← add_smul]; simp
  · by_cases hB : IsBip H lab F (v, K)
    · exfalso
      have hc := col_proper hB huK hwK huw
      have h1' := fun x => h1 ⟨hB, x⟩
      have h2' := fun x => h2 ⟨hB, x⟩
      revert hc h1' h2'
      cases col H lab F (v, K) u <;> cases col H lab F (v, K) w <;>
        cases col H lab F (v, K) h.choose <;> simp
    · rw [← add_smul]
      exact two_dl_core hCt ht ht3 hv hKa hB h.choose_spec.1 h.choose_spec.2
  · simp

/-- the transport of an active vertex of `W` agrees with `δ_u` modulo the core image -/
theorem dl_sub_rho (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {u w : V} (huw : (link H lab F v).Adj u w) (huW : u ∈ W) :
    dl u - rho H lab F W v u ∈ starIm (indG H W) lab F v := by
  unfold rho
  set K := comp H lab F v u with hK
  have hKa : K ∈ S07V25.activeComps H lab F v := mem_activeComps_of_active huw
  have huK : u ∈ K := self_mem_comp v u
  have hex : ∃ z, z ∈ K ∧ z ∈ W := ⟨u, huK, huW⟩
  unfold rhoK
  rw [dif_pos hex]
  set z := hex.choose with hz
  have hzK : z ∈ K := hex.choose_spec.1
  have hzW : z ∈ W := hex.choose_spec.2
  by_cases huz : u = z
  · rw [if_neg (by rw [← huz]; simp), one_smul, huz, sub_self]
    exact Submodule.zero_mem _
  by_cases hB : IsBip H lab F (v, K)
  · by_cases hcol : col H lab F (v, K) u ≠ col H lab F (v, K) z
    · rw [if_pos ⟨hB, hcol⟩, neg_one_smul, sub_neg_eq_add]
      have hadm : OrigAdm H lab F v u z := by
        refine ⟨K, hKa, huK, hzK, huz, fun _ => ?_⟩
        rw [colG_eq hKa huK, colG_eq hKa hzK]; exact hcol
      exact adm_starIm hCt ht hv hadm huW hzW
    · rw [if_neg (fun h => hcol h.2), one_smul]
      push_neg at hcol
      obtain ⟨n, -, hzn, -, -⟩ := core_nbr hCt ht3 hv hKa hzK hzW
      have hnL := link_indG_le v hzn
      have hnK : n ∈ K := mem_of_adj hKa hzK hnL.reachable
      have hnW : n ∈ W := (link_indG_adj.1 hzn).2.2.2
      have hcn : col H lab F (v, K) z ≠ col H lab F (v, K) n := col_proper hB hzK hnK hnL
      have hadm : OrigAdm H lab F v u n := by
        refine ⟨K, hKa, huK, hnK, fun h => ?_, fun _ => ?_⟩
        · subst h; exact hcn hcol.symm
        · rw [colG_eq hKa huK, colG_eq hKa hnK, hcol]; exact hcn
      have e1 := adm_starIm hCt ht hv hadm huW hnW
      have e2 := adj_mem_starIm (indG H W) lab F hzn
      have := Submodule.sub_mem _ e1 e2
      have e : dl u + dl n - (dl z + dl n) = dl u - dl z := by abel
      rwa [e] at this
  · rw [if_neg (fun h => hB h.1), one_smul]
    have hadm : OrigAdm H lab F v u z := ⟨K, hKa, huK, hzK, huz, fun h => absurd h hB⟩
    have e1 := adm_starIm hCt ht hv hadm huW hzW
    have e2 := two_dl_core hCt ht ht3 hv hKa hB hzK hzW
    have := Submodule.sub_mem _ e1 e2
    have e : dl u + dl z - (2 : ℤ) • dl z = dl u - dl z := by rw [two_smul]; abel
    rwa [e] at this

lemma linComb_dl (r : V → V → ℤ) (u : V) : Fintype.linearCombination ℤ r (dl u) = r u := by
  rw [Fintype.linearCombination_apply]
  simp [dl, Pi.single_apply]

/-- **integral star transfer into the core** -/
theorem starIm_core_of_orig (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    {v : V} (hv : v ∈ W) {f : V → ℤ} (hf : f ∈ starIm H lab F v)
    (hact : ∀ u, f u ≠ 0 → u ∈ W ∧ LinkActive H lab F v u) :
    f ∈ starIm (indG H W) lab F v := by
  set L := Fintype.linearCombination ℤ (rho H lab F W v)
  have h1 : L f ∈ starIm (indG H W) lab F v := by
    have hle : starIm H lab F v ≤ (starIm (indG H W) lab F v).comap L := by
      rw [starIm, Submodule.span_le]
      rintro _ ⟨⟨T, hT⟩, rfl⟩
      simp only [triAt, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      obtain ⟨hTa, hvT⟩ := hT
      obtain ⟨u, huT, huv⟩ : ∃ u ∈ T, u ≠ v := by
        by_contra hc
        push_neg at hc
        have hsub : T ⊆ {v} := fun y hy => by rw [Finset.mem_singleton]; exact hc y hy
        have := card_le_card hsub
        rw [Finset.card_singleton, hTa.1] at this
        omega
      obtain ⟨w, huw, rfl⟩ := tri_decomp hTa hvT huT huv
      have hwv : w ≠ v := by
        obtain ⟨-, h, -⟩ := distinct_of_card_three hTa.1
        exact fun e => h e.symm
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show L (triVec v {v, u, w}) ∈ _
      rw [triVec_triple huw.ne huv hwv, map_add, linComb_dl, linComb_dl]
      unfold rho
      have hw : comp H lab F v w = comp H lab F v u :=
        comp_eq_of_mem H lab F ((mem_comp_iff H lab F).2 huw.reachable)
      rw [hw]
      exact rhoK_edge hCt ht ht3 hv huw
    exact hle hf
  have h2 : f - L f ∈ starIm (indG H W) lab F v := by
    have hfs : f = ∑ u, f u • dl u := by
      funext a
      simp [Finset.sum_apply, dl, Pi.single_apply]
    have : f - L f = ∑ u, f u • (dl u - rho H lab F W v u) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← hfs, Fintype.linearCombination_apply]
    rw [this]
    refine Submodule.sum_mem _ fun u _ => ?_
    by_cases hu : f u = 0
    · rw [hu, zero_smul]; exact Submodule.zero_mem _
    · obtain ⟨huW, w, huw⟩ := hact u hu
      exact Submodule.smul_mem _ _ (dl_sub_rho hCt ht ht3 hv huw huW)
  have := Submodule.add_mem _ h2 h1
  rwa [sub_add_cancel] at this

/-! ### From local profiles to star vectors and back -/

/-- the star vector of an edge vector at `v` -/
def star (x : Sym2 V → ℤ) (v : V) : V → ℤ := fun u => if u = v then 0 else x s(v, u)

omit [Fintype V] in
lemma star_ne {x : Sym2 V → ℤ} {v u : V} (h : u ≠ v) : star x v u = x s(v, u) := if_neg h

lemma star_mem_starIm (G : SimpleGraph V) {x : Sym2 V → ℤ} (hx : IsLocalProfile G lab F x)
    (v : V) : star x v ∈ starIm G lab F v := by
  obtain ⟨c, hc⟩ := hx.2 v
  rw [starIm, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun T => c T.1, ?_⟩
  funext u
  rw [Finset.sum_apply]
  symm
  by_cases huv : u = v
  · subst huv
    simp [star, triVec]
  · rw [star_ne huv, hc u huv]
    change ∑ T ∈ (triAt G lab F v).filter (u ∈ ·), c T = _
    rw [Finset.sum_filter, ← Finset.sum_coe_sort (triAt G lab F v)]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases huT : u ∈ T.1
    · simp [triVec, huT, huv]
    · simp [triVec, huT]

lemma localProfile_at_of_starIm (G : SimpleGraph V) {x : Sym2 V → ℤ} {v : V}
    (hs : star x v ∈ starIm G lab F v) :
    ∃ c : Finset V → ℤ, ∀ w, w ≠ v →
      x s(v, w) = ∑ T ∈ ((univ.filter (IsAllowed G lab F)).filter (v ∈ ·)).filter (w ∈ ·),
        c T := by
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hs
  refine ⟨fun T => if h : T ∈ triAt G lab F v then c' ⟨T, h⟩ else 0, fun u hu => ?_⟩
  rw [← star_ne (x := x) hu, ← hc', Finset.sum_apply]
  change _ = ∑ T ∈ (triAt G lab F v).filter (u ∈ ·), _
  rw [Finset.sum_filter, ← Finset.sum_coe_sort (triAt G lab F v)]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [Pi.smul_apply, triVec, smul_eq_mul, Finset.coe_mem, dif_pos, Subtype.coe_eta]
  by_cases huT : u ∈ T.1
  · simp [huT, hu]
  · simp [huT]

/-! ### Item 3: the profile transfer -/

/-- **intrinsic local-profile transfer into the core**: an integer edge vector supported on the
edges of `H[W]` and lying in the ORIGINAL local profile module lies in `MCore H lab F W`. -/
theorem mem_MCore_of_contract (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    {x : Sym2 V → ℤ} (hx : x ∈ localProfile H lab F)
    (hsupp : ∀ e, e ∉ edges (indG H W) → x e = 0) : x ∈ MCore H lab F W := by
  refine ⟨hsupp, fun v => ?_⟩
  by_cases hv : v ∈ W
  · apply localProfile_at_of_starIm
    refine starIm_core_of_orig hCt ht ht3 hv (star_mem_starIm H hx v) fun u hu => ?_
    have huv : u ≠ v := fun h => hu (by rw [h]; simp [star])
    rw [star_ne huv] at hu
    have hE : s(v, u) ∈ edges (indG H W) := by
      by_contra hc; exact hu (hsupp _ hc)
    rw [mem_edges, SimpleGraph.mem_edgeSet] at hE
    refine ⟨hE.2.2, ?_⟩
    obtain ⟨c, hc⟩ := hx.2 v
    rw [hc u huv] at hu
    obtain ⟨T, hT, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨w, huw, -⟩ := tri_decomp hT.1.1 hT.1.2 hT.2 huv
    exact ⟨w, huw⟩
  · refine ⟨0, fun w _ => ?_⟩
    simp only [Pi.zero_apply, Finset.sum_const_zero]
    apply hsupp
    rw [mem_edges, SimpleGraph.mem_edgeSet]
    exact fun h => hv h.2.1

/-- **ambient-physical, core-supported vectors lie in `MCore`** -/
theorem mem_MCore_of_lattice (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t)
    {x : Sym2 V → ℤ} (hx : x ∈ lattice H lab F)
    (hsupp : ∀ e, e ∉ edges (indG H W) → x e = 0) : x ∈ MCore H lab F W :=
  mem_MCore_of_contract hCt ht ht3 (lattice_le_localProfile H lab F hx) hsupp

end S07V45
