/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Generation
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §4' — adapter: compression data on the TRUE subtype host ⇒ ambient compression data

`HostCompression G lab F d c E` is the G1-Z export shape for an arbitrary host `G` on a finite
type: a coordinate map on the actual local profile module with kernel in the actual lattice,
coordinate bound `c · l1E`, and image identity with generators in `[-E, E]^d`.

* `HostCompression.transport`: for `ι : X → V` injective and a host `G` on `V` all of whose edges
  have ends in the image of `ι`, compression data of the true induced host `G.comap ι` give
  compression data of `G` with the SAME constants (local profiles, lattices and `l1E`
  correspond exactly under zero extension, `isLocalProfile_pull`, `lattice_pull`).
* `CoreCompression.ofSubtype`: from compression data of the true core host
  `H.comap (Subtype.val : {x // x ∈ W} → V)`.
* `DelCompression.ofSubtype`: from compression data of the true deleted host
  `H.comap (Subtype.val : {x // x ∉ Z} → V)` (`= H[V \ Z]`).

So the named compression inputs of §4 may be supplied on true subtypes.
-/

open Finset Classical Submodule

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.Dispersal

variable {X V I : Type*}

/-- **Compression data of a host** (G1-Z export shape). -/
structure HostCompression [Fintype X] (G : SimpleGraph X) (lab : X → I) (F : Set (Multiset I))
    (d c E : ℕ) where
  /-- coordinate map on the actual local profile module -/
  q : localProfile G lab F →ₗ[ℤ] (Fin d → ℤ)
  /-- kernel inside the actual lattice -/
  ker_le : ∀ x : localProfile G lab F, q x = 0 → (x : Sym2 X → ℤ) ∈ lattice G lab F
  /-- coordinate bound -/
  bound : ∀ (x : localProfile G lab F) (i : Fin d), |q x i| ≤ c * l1E (x : Sym2 X → ℤ)
  /-- generators of the image of the lattice -/
  S : Finset (Fin d → ℤ)
  /-- bounded generators -/
  S_bound : ∀ s ∈ S, ∀ i, |s i| ≤ E
  /-- image identity -/
  img : ((lattice G lab F).comap (localProfile G lab F).subtype).map q =
    span ℤ (S : Set (Fin d → ℤ))

section transport

variable [Fintype X] [Fintype V] {ι : X → V} (hι : Function.Injective ι)

/-- restriction of edge vectors along `Sym2.map ι` -/
def pullL (ι : X → V) : (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 X → ℤ) where
  toFun x := x ∘ Sym2.map ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype X] [Fintype V] in
lemma liftE_ind (K : Finset (Sym2 X)) : liftE (ι := ι) (ind K) = ind (K.map (emb2 hι)) := by
  funext e
  by_cases h : ∃ e', Sym2.map ι e' = e
  · obtain ⟨e', rfl⟩ := h
    rw [liftE_map hι]
    simp only [ind, Finset.mem_map, emb2_apply]
    congr 1
    exact propext ⟨fun h => ⟨e', h, rfl⟩, fun ⟨a, ha, hae⟩ => Sym2.map.injective hι hae ▸ ha⟩
  · rw [liftE_of_not (ι := ι) _ h]
    simp only [ind, Finset.mem_map, emb2_apply]
    rw [if_neg]
    rintro ⟨a, -, rfl⟩; exact h ⟨a, rfl⟩

omit [Fintype X] [Fintype V] in
lemma pull_ind (K : Finset (Sym2 X)) : pullL ι (ind (K.map (emb2 hι))) = ind K := by
  funext e
  simp only [pullL, LinearMap.coe_mk, AddHom.coe_mk, Function.comp, ind, Finset.mem_map,
    emb2_apply]
  congr 1
  exact propext ⟨fun ⟨a, ha, hae⟩ => Sym2.map.injective hι hae ▸ ha, fun h => ⟨e, h, rfl⟩⟩

variable {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

omit [Fintype X] [Fintype V] in
include hι in
lemma liftE_lattice {y : Sym2 X → ℤ} (hy : y ∈ lattice (G.comap ι) (lab ∘ ι) F) :
    liftE (ι := ι) y ∈ lattice G lab F := by
  have : y ∈ (lattice G lab F).comap (liftL ι hι) := by
    unfold lattice at hy ⊢
    refine (span_le.2 ?_) hy
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, liftL_apply, liftE_ind hι, ← triEdges_map]
    exact subset_span ⟨_, (isAllowed_comap_iff hι T).1 hT, rfl⟩
  exact this

omit [Fintype X] [Fintype V] in
include hι in
lemma pull_lattice (hG : EdgesIn G ι) {x : Sym2 V → ℤ} (hx : x ∈ lattice G lab F) :
    pullL ι x ∈ lattice (G.comap ι) (lab ∘ ι) F := by
  have : x ∈ (lattice (G.comap ι) (lab ∘ ι) F).comap (pullL ι) := by
    unfold lattice at hx ⊢
    refine (span_le.2 ?_) hx
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨T', rfl⟩ : ∃ T' : Finset X, T'.map (emb hι) = T := by
      obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.1 (by rw [hT.1]; norm_num)
      exact exists_map_of_allowed hι hG hT hv
    rw [SetLike.mem_coe, Submodule.mem_comap]
    beta_reduce
    rw [triEdges_map, pull_ind hι]
    exact subset_span ⟨T', (isAllowed_comap_iff hι T').2 hT, rfl⟩
  exact this

/-- the restriction map between local profile modules -/
def pullLP (hG : EdgesIn G ι) :
    localProfile G lab F →ₗ[ℤ] localProfile (G.comap ι) (lab ∘ ι) F where
  toFun x := ⟨pullL ι x, (isLocalProfile_pull hι hG x.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Transport of compression data along a true induced subhost.** -/
def HostCompression.transport (hG : EdgesIn G ι) {d c E : ℕ}
    (C : HostCompression (G.comap ι) (lab ∘ ι) F d c E) : HostCompression G lab F d c E where
  q := C.q.comp (pullLP hι hG)
  ker_le x hx := by
    have h1 := C.ker_le _ hx
    have h2 := liftE_lattice hι h1
    have h3 := (isLocalProfile_pull hι hG x.2).2
    simp only [pullLP, LinearMap.coe_mk, AddHom.coe_mk] at h2
    exact h3 ▸ h2
  bound x i := by
    have h := C.bound (pullLP hι hG x) i
    have h3 := (isLocalProfile_pull hι hG x.2).2
    have hl : l1E ((pullLP hι hG x : localProfile (G.comap ι) (lab ∘ ι) F) : Sym2 X → ℤ) =
        l1E (x : Sym2 V → ℤ) := by
      conv_rhs => rw [← h3]
      rw [l1E_liftE hι]; rfl
    rw [hl] at h; exact h
  S := C.S
  S_bound := C.S_bound
  img := by
    rw [← C.img]
    ext v
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨x, hxL, rfl⟩
      exact ⟨pullLP hι hG x, pull_lattice hι hG hxL, rfl⟩
    · rintro ⟨y, hyL, rfl⟩
      refine ⟨⟨liftE (ι := ι) y, isLocalProfile_liftE hι hG y.2⟩, liftE_lattice hι hyL, ?_⟩
      congr 1
      apply Subtype.ext
      funext e
      show liftE (ι := ι) (y : Sym2 X → ℤ) (Sym2.map ι e) = (y : Sym2 X → ℤ) e
      exact liftE_map hι _ e

end transport

variable [Fintype V] {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- **core compression data from the TRUE core subtype host** -/
def CoreCompression.ofSubtype {W : Finset V} {d c E : ℕ}
    (C : HostCompression (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F d c E) :
    CoreCompression H lab F W d c E :=
  let C' : HostCompression ((indG H W).comap (Subtype.val : {x // x ∈ W} → V))
      (lab ∘ Subtype.val) F d c E := (indG_comap H W).symm ▸ C
  let T := C'.transport Subtype.val_injective (edgesIn_indG H W)
  ⟨T.q, T.ker_le, T.bound, T.S, T.S_bound, T.img⟩

omit [Fintype V] in
lemma delG_comap (H : SimpleGraph V) (Z : Finset V) :
    (S07V39.delG H Z).comap (Subtype.val : {x // x ∉ Z} → V) = H.comap Subtype.val := by
  ext a b
  simp only [SimpleGraph.comap_adj, S07V39.delG]
  exact ⟨fun h => h.1, fun h => ⟨h, a.2, b.2⟩⟩

omit [Fintype V] in
lemma edgesIn_delG (H : SimpleGraph V) (Z : Finset V) :
    EdgesIn (S07V39.delG H Z) (Subtype.val : {x // x ∉ Z} → V) :=
  fun a _ h => ⟨⟨a, h.2.1⟩, rfl⟩

/-- **deleted-host compression data from the TRUE subtype host `H[V \ Z]`** -/
def DelCompression.ofSubtype {Z : Finset V} {d c E : ℕ}
    (C : HostCompression (H.comap (Subtype.val : {x // x ∉ Z} → V)) (lab ∘ Subtype.val) F d c E) :
    DelCompression H lab F Z d c E :=
  let C' : HostCompression ((S07V39.delG H Z).comap (Subtype.val : {x // x ∉ Z} → V))
      (lab ∘ Subtype.val) F d c E := (delG_comap H Z).symm ▸ C
  let T := C'.transport Subtype.val_injective (edgesIn_delG H Z)
  ⟨T.q, T.ker_le, T.bound, T.S, T.S_bound, T.img⟩

end S07V42
