/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SlotPairing
public import RequestProject.TypedTriangle.SparseEdgeDefs
public import RequestProject.TypedTriangle.SeedTransport
public import RequestProject.TypedTriangle.RestrictedHingeTransport
public import RequestProject.TypedTriangle.VortexRestrictedEdgeLoad
public import RequestProject.TypedTriangle.VortexNestedH4Transport
public import RequestProject.S07V42.Setting
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.ReferenceTrim

variable {V I : Type*} [Fintype V]

/-- The nested survivor type of the sampled reference is the direct trimmed
window used by the physical child. -/
def nestedToDirectTrim (W : Finset V) (A : Finset {x // x ∈ W}) :
    Survivors A ≃ {v : V // v ∈ W \ A.image Subtype.val} where
  toFun x := ⟨x.1.1, by
    refine mem_sdiff.mpr ⟨x.1.2, ?_⟩
    intro hx
    obtain ⟨a,ha,hav⟩ := mem_image.mp hx
    have heq : a = x.1 := Subtype.ext hav
    exact x.2 (heq ▸ ha)⟩
  invFun y := ⟨⟨y.1,(mem_sdiff.mp y.2).1⟩,by
    intro hy
    exact (mem_sdiff.mp y.2).2 (mem_image.mpr
      ⟨⟨y.1,(mem_sdiff.mp y.2).1⟩,hy,rfl⟩)⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro y; apply Subtype.ext; rfl

/-- The agenda's survivor type for deleting the complement of `W` is
canonically the vertex type of the sampled reference on `W`. -/
def scheduledToWindow (W : Finset V) :
    Survivors (univ \ W) ≃ {x : V // x ∈ W} where
  toFun x := ⟨x.1, by simpa using x.2⟩
  invFun x := ⟨x.1, by simpa using x.2⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

theorem scheduled_trim_card (W : Finset V)
    (A : Finset (Survivors (univ \ W))) :
    (A.image (scheduledToWindow W)).card = A.card := by
  exact Finset.card_image_of_injective A (scheduledToWindow W).injective

theorem scheduled_trim_ambient (W : Finset V)
    (A : Finset (Survivors (univ \ W))) :
    ((A.image (scheduledToWindow W)).image Subtype.val) =
      A.image (fun x : Survivors (univ \ W) => x.1) := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z,hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(scheduledToWindow W) z,⟨z,hz,rfl⟩,rfl⟩

/-- Relabelling by an equivalence preserves incident edge counts. -/
theorem degree_image_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (B : Finset (Sym2 X)) (v : X) :
    SparseEdge.degIn (B.image (Sym2.map e)) (e v) =
      SparseEdge.degIn B v := by
  have hfilter : ((B.image (Sym2.map e)).filter (fun f => e v ∈ f)) =
      (B.filter (fun f => v ∈ f)).image (Sym2.map e) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨g,hg,rfl⟩,hvg⟩
      obtain ⟨w,hw,hew⟩ := Sym2.mem_map.mp hvg
      have hwv : w = v := e.injective hew
      exact ⟨g,⟨hg,hwv ▸ hw⟩,rfl⟩
    · rintro ⟨g,⟨hg,hvg⟩,rfl⟩
      exact ⟨⟨g,hg,rfl⟩,Sym2.mem_map.mpr ⟨v,hvg,rfl⟩⟩
  simp only [SparseEdge.degIn, hfilter,
    Finset.card_image_of_injective _ (Sym2.map.injective e.injective)]

theorem degree_mono {X : Type*} [Fintype X]
    {B C : Finset (Sym2 X)} (h : B ⊆ C) (v : X) :
    SparseEdge.degIn B v ≤ SparseEdge.degIn C v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- The complement of a reference in a host, and hence its local degree,
is invariant under exact relabelling of the host. -/
theorem holes_degree_equiv {X Y I₀ : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (H₁ : Host X I₀) (H₂ : Host Y I₀)
    (B : Finset (Sym2 X))
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (v : X) :
    SparseEdge.degIn (edges H₂ \ B.image (Sym2.map e)) (e v) =
      SparseEdge.degIn (edges H₁ \ B) v := by
  have hEdgeIff (f : Sym2 X) :
      f ∈ edges H₁ ↔ Sym2.map e f ∈ edges H₂ := by
    induction f using Sym2.ind with
    | _ x y => simpa [edges] using hAdj x y
  have hEdges : edges H₂ = (edges H₁).image (Sym2.map e) := by
    ext f
    constructor
    · intro hf
      let g := Sym2.map e.symm f
      have hfg : Sym2.map e g = f := by
        induction f using Sym2.ind with
        | _ x y => simp [g]
      refine Finset.mem_image.mpr ⟨g, ?_, hfg⟩
      apply (hEdgeIff g).2
      simpa only [hfg] using hf
    · intro hf
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
      exact (hEdgeIff g).1 hg
  have hHoles : edges H₂ \ B.image (Sym2.map e) =
      (edges H₁ \ B).image (Sym2.map e) := by
    rw [hEdges]
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨⟨g,hg,hgf⟩,hnot⟩
      exact ⟨g,⟨hg,fun hgB => hnot ⟨g,hgB,hgf⟩⟩,hgf⟩
    · rintro ⟨g,⟨hg,hnot⟩,hgf⟩
      refine ⟨⟨g,hg,hgf⟩,?_⟩
      rintro ⟨g',hg'B,hg'f⟩
      have hgg' : g = g' := (Sym2.map.injective e.injective)
        (hgf.trans hg'f.symm)
      exact hnot (hgg'.symm ▸ hg'B)
  rw [hHoles, degree_image_equiv]

/-- Keep exactly those blocks of a decomposition that stay in a smaller vertex set. -/
def blocks (D : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  D.filter (· ⊆ U)

/-- The edge set of the surviving blocks. -/
def keptEdges (D : Finset (Finset V)) (U : Finset V) : Finset (Sym2 V) :=
  (blocks D U).biUnion triEdges

theorem decomposition (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (U : Finset V)
    (hD : IsDecomposition H F E D) :
    IsDecomposition H F (keptEdges D U) (blocks D U) := by
  refine ⟨?_, ?_, rfl⟩
  · intro T hT
    exact hD.1 T (mem_filter.mp hT).1
  · intro T hT S hS hTS
    exact hD.2.1 (mem_filter.mp hT).1 (mem_filter.mp hS).1 hTS

theorem basal (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (U : Finset V)
    (hD : IsDecomposition H F E D) : Basal H F (keptEdges D U) :=
  ⟨blocks D U, decomposition H F E D U hD⟩

/-- Pull the trimmed reference into the actual survivor subtype.  Applied
with `H` equal to the sampled host on `W`, this is the decomposition on the
nested subtype obtained after deleting `A`. -/
theorem decomposition_on_survivors (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (A : Finset V)
    (hD : IsDecomposition H F E D) :
    IsDecomposition (restrictedHost H A) F
      (restrictEdgeSet A (keptEdges D (univ \ A)))
      ((blocks D (univ \ A)).image
        (fun T => T.subtype (fun v => v ∉ A))) := by
  have hTrim := decomposition H F E D (univ \ A) hD
  have hEdge : keptEdges D (univ \ A) ⊆ edges (vertexDeleted H A) := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    obtain ⟨hTD,hTA⟩ := mem_filter.mp hT
    have hAvoid : Disjoint T A := by
      apply disjoint_left.mpr
      intro x hx hxA
      exact (mem_sdiff.mp (hTA hx)).2 hxA
    have hAllowed : IsAllowed (vertexDeleted H A) F T :=
      (isAllowed_vertexDeleted_iff H F A T).mpr ⟨hD.1 T hTD,hAvoid⟩
    exact triEdges_subset_edges hAllowed heT
  exact isDecomposition_restrictEdgeSet H F A hTrim hEdge

theorem basal_on_survivors (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (A : Finset V)
    (hD : IsDecomposition H F E D) :
    Basal (restrictedHost H A) F
      (restrictEdgeSet A (keptEdges D (univ \ A))) :=
  ⟨_, decomposition_on_survivors H F E D A hD⟩

/-- The actual reference after trimming, transported from nested survivors
to the direct subtype of `W \ A` expected by the paid-child theorem. -/
theorem decomposition_on_direct_trim (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (A : Finset {x // x ∈ W})
    (E : Finset (Sym2 {x // x ∈ W}))
    (D : Finset (Finset {x // x ∈ W}))
    (hD : IsDecomposition
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)
      F E D) :
    letI : DecidableEq {x // x ∈ W} := Classical.decEq _
    let W' := W \ A.image Subtype.val
    let J' : Host {x // x ∈ W'} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let e := nestedToDirectTrim W A
    IsDecomposition J' F
      ((restrictEdgeSet A (keptEdges D (univ \ A))).image (Sym2.map e))
      (((blocks D (univ \ A)).image
        (fun T => T.subtype (fun v => v ∉ A))).image
        (fun T => T.map e.toEmbedding)) := by
  let J : Host {x // x ∈ W} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  let W' := W \ A.image Subtype.val
  let J' : Host {x // x ∈ W'} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let e := nestedToDirectTrim W A
  have hN := decomposition_on_survivors J F E D A hD
  have hMap := Vortex.isDecomposition_map_equiv e (restrictedHost J A) J' F
    (fun _ _ => Iff.rfl) (fun _ => rfl) _ _ hN
  convert hMap using 1
  · ext x
    simp only [Finset.mem_image]
    rfl
  · ext x
    simp only [Finset.mem_image]
    rfl

theorem basal_on_direct_trim (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (A : Finset {x // x ∈ W})
    (E : Finset (Sym2 {x // x ∈ W}))
    (D : Finset (Finset {x // x ∈ W}))
    (hD : IsDecomposition
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)
      F E D) :
    letI : DecidableEq {x // x ∈ W} := Classical.decEq _
    let W' := W \ A.image Subtype.val
    let J' : Host {x // x ∈ W'} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let e := nestedToDirectTrim W A
    Basal J' F
      ((restrictEdgeSet A (keptEdges D (univ \ A))).image (Sym2.map e)) :=
  ⟨_, decomposition_on_direct_trim H F W A E D hD⟩

theorem kept_subset (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (U : Finset V)
    (hD : IsDecomposition H F E D) : keptEdges D U ⊆ E := by
  intro e he
  obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
  exact hD.subset (mem_filter.mp hT).1 heT

private theorem third_unique {T : Finset V} {v w a w' : V}
    (hT : T.card = 3) (hv : v ∈ T) (hw : w ∈ T)
    (ha : a ∈ T) (hw' : w' ∈ T)
    (hvw : v ≠ w) (hva : v ≠ a) (hwa : w ≠ a)
    (hw'v : w' ≠ v) (hw'a : w' ≠ a) : w = w' := by
  by_contra hww'
  exact card_four_le_three hT hv hw ha hw' hvw hva hwa hw'v (Ne.symm hww') hw'a

private theorem edge_avoiding_vertex_unique {T : Finset V} {a : V}
    {e f : Sym2 V} (hT : T.card = 3) (ha : a ∈ T)
    (heT : e ∈ triEdges T) (hfT : f ∈ triEdges T)
    (hae : a ∉ e) (haf : a ∉ f) : e = f := by
  have hTe : (T.erase a).card = 2 := by
    rw [card_erase_of_mem ha, hT]
  have heSub : e.toFinset ⊆ T.erase a := by
    intro x hx
    exact mem_erase.mpr ⟨by
      intro h; subst x; exact hae (Sym2.mem_toFinset.mp hx),
      toFinset_subset_of_mem_triEdges heT hx⟩
  have hfSub : f.toFinset ⊆ T.erase a := by
    intro x hx
    exact mem_erase.mpr ⟨by
      intro h; subst x; exact haf (Sym2.mem_toFinset.mp hx),
      toFinset_subset_of_mem_triEdges hfT hx⟩
  have heCard := Sym2.card_toFinset_of_not_isDiag e (not_isDiag_of_mem_triEdges heT)
  have hfCard := Sym2.card_toFinset_of_not_isDiag f (not_isDiag_of_mem_triEdges hfT)
  have heEq : e.toFinset = T.erase a :=
    Finset.eq_of_subset_of_card_le heSub (by omega)
  have hfEq : f.toFinset = T.erase a :=
    Finset.eq_of_subset_of_card_le hfSub (by omega)
  exact eq_of_toFinset_eq (heEq.trans hfEq.symm)

/-- An interior edge lost when whole triangles are trimmed has a unique
covering triangle, and that triangle meets the deleted vertex set. -/
private theorem loss_witness (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (W A : Finset V)
    (hD : IsDecomposition H F E D)
    (hDW : ∀ T ∈ D, T ⊆ W) (v : V)
    (e : Sym2 V)
    (he : e ∈ (SparseEdge.edges (S07V42.indG H.G (W \ A)) \ keptEdges D (W \ A)).filter
      (fun f => v ∈ f)) (heE : e ∈ E) :
    ∃ T ∈ D, ∃ a ∈ A, e ∈ triEdges T ∧ v ∈ T ∧ a ∈ T ∧
      v ≠ a ∧ a ∉ e ∧ s(v,a) ∈ E := by
  have heD := hD.exists_mem heE
  obtain ⟨T,hT,heT⟩ := heD
  obtain ⟨heS,hvE⟩ := mem_filter.mp he
  obtain ⟨heInd,heNot⟩ := mem_sdiff.mp heS
  have hvT : v ∈ T := by
    induction e using Sym2.ind with
    | _ x y =>
      rcases (by simpa using hvE : v = x ∨ v = y) with rfl | rfl
      · exact (mem_triEdges.mp heT).1
      · exact (mem_triEdges.mp heT).2.1
  have hNotU : ¬ T ⊆ W \ A := by
    intro hTU
    apply heNot
    exact mem_biUnion.mpr ⟨T,mem_filter.mpr ⟨hT,hTU⟩,heT⟩
  have hA : ∃ a ∈ T, a ∉ W \ A := by
    by_contra hn
    apply hNotU
    intro a ha
    by_contra haU
    exact hn ⟨a,ha,haU⟩
  obtain ⟨a,haT,haU⟩ := hA
  have haA : a ∈ A := by
    by_contra haA
    exact haU (mem_sdiff.mpr ⟨hDW T hT haT,haA⟩)
  have haNotE : a ∉ e := by
    induction e using Sym2.ind with
    | _ x y =>
      have hAdj : (S07V42.indG H.G (W \ A)).Adj x y := by
        simpa [SparseEdge.edges] using heInd
      have hEnds := hAdj.2
      simpa using (show a ≠ x ∧ a ≠ y from ⟨
        fun h => haU (h ▸ hEnds.1), fun h => haU (h ▸ hEnds.2)⟩)
  have hva : v ≠ a := by
    intro h; subst a
    exact haNotE hvE
  have hVA : s(v,a) ∈ E :=
    hD.subset hT (mem_triEdges.mpr ⟨hvT,haT,hva⟩)
  exact ⟨T,hT,a,haA,heT,hvT,haT,hva,haNotE,hVA⟩

private theorem loss_vertex (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (W A : Finset V)
    (hD : IsDecomposition H F E D)
    (hDW : ∀ T ∈ D, T ⊆ W) (v : V)
    (e : Sym2 V)
    (he : e ∈ ((SparseEdge.edges (S07V42.indG H.G (W \ A)) \ keptEdges D (W \ A)) ∩ E).filter
      (fun f => v ∈ f)) :
    ∃ a ∈ A, ∃ T ∈ D, e ∈ triEdges T ∧ v ∈ T ∧ a ∈ T ∧
      v ≠ a ∧ a ∉ e := by
  obtain ⟨heInt,hv⟩ := mem_filter.mp he
  obtain ⟨heK,heE⟩ := mem_inter.mp heInt
  obtain ⟨T,hT,a,ha,heT,hvT,haT,hva,hae,_⟩ :=
    loss_witness H F E D W A hD hDW v e (mem_filter.mpr ⟨heK,hv⟩) heE
  exact ⟨a,ha,T,hT,heT,hvT,haT,hva,hae⟩

/-- Each newly missing interior edge at `v` can be charged to a distinct
deleted vertex. The charge is the edge `va` in the original edge-disjoint
triangle decomposition. -/
theorem loss_degree_le_deleted_card (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (W A : Finset V)
    (hD : IsDecomposition H F E D)
    (hDW : ∀ T ∈ D, T ⊆ W) (v : V) :
    (((SparseEdge.edges (S07V42.indG H.G (W \ A)) \ keptEdges D (W \ A)) ∩ E).filter
      (fun e => v ∈ e)).card ≤ A.card := by
  let L := ((SparseEdge.edges (S07V42.indG H.G (W \ A)) \ keptEdges D (W \ A)) ∩ E).filter
      (fun e => v ∈ e)
  let a : Sym2 V → V := fun e =>
    if he : e ∈ L then Classical.choose (loss_vertex H F E D W A hD hDW v e he)
    else v
  change L.card ≤ A.card
  apply Finset.card_le_card_of_injOn a
  · intro e he
    change e ∈ L at he
    change a e ∈ A
    simp only [a, dif_pos he]
    exact (Classical.choose_spec (loss_vertex H F E D W A hD hDW v e he)).1
  · intro e he f hf hef
    change e ∈ L at he
    change f ∈ L at hf
    have hfe : a e = a f := hef
    have hEa := Classical.choose_spec (loss_vertex H F E D W A hD hDW v e he)
    have hFa := Classical.choose_spec (loss_vertex H F E D W A hD hDW v f hf)
    obtain ⟨Te,hTe,heTe,hvTe,haTe,hvaE,hae⟩ := hEa.2
    obtain ⟨Tf,hTf,hfTf,hvTf,haTf,hvaF,haf⟩ := hFa.2
    have hAe : a e = Classical.choose (loss_vertex H F E D W A hD hDW v e he) := by
      simp only [a, dif_pos he]
    have hAf : a f = Classical.choose (loss_vertex H F E D W A hD hDW v f hf) := by
      simp only [a, dif_pos hf]
    rw [← hAe] at haTe hvaE hae
    rw [← hAf, ← hfe] at haTf hvaF haf
    have hTeq : Te = Tf := hD.unique hTe hTf
      (mem_triEdges.mpr ⟨hvTe,haTe,hvaE⟩)
      (mem_triEdges.mpr ⟨hvTf,haTf,hvaF⟩)
    subst Tf
    exact edge_avoiding_vertex_unique (hD.1 Te hTe).1 haTe heTe hfTf hae haf

theorem holes_subset (K L E E' : Finset (Sym2 V))
    (hKL : K ⊆ L) (hE' : E' ⊆ E) :
    K \ E' ⊆ (L \ E) ∪ (E \ E') := by
  intro e he
  rcases mem_sdiff.mp he with ⟨heK, hne'⟩
  by_cases heE : e ∈ E
  · exact mem_union_right _ (mem_sdiff.mpr ⟨heE, hne'⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hKL heK, heE⟩)

theorem holes_degree_le (K L E E' : Finset (Sym2 V))
    (hKL : K ⊆ L) (hE' : E' ⊆ E) (v : V) :
    SparseEdge.degIn (K \ E') v ≤
      SparseEdge.degIn (L \ E) v + SparseEdge.degIn (E \ E') v := by
  have h := holes_subset K L E E' hKL hE'
  have hfirst := Finset.card_le_card (Finset.filter_subset_filter (v ∈ ·) h)
  rw [Finset.filter_union] at hfirst
  have hcard := hfirst.trans
    (Finset.card_union_le ((L \ E).filter (v ∈ ·)) ((E \ E').filter (v ∈ ·)))
  simpa only [SparseEdge.degIn, Finset.filter_union] using hcard

private theorem holes_degree_le_local (K L E E' : Finset (Sym2 V))
    (hKL : K ⊆ L) (v : V) :
    SparseEdge.degIn (K \ E') v ≤ SparseEdge.degIn (L \ E) v +
      (((K \ E') ∩ E).filter (fun e => v ∈ e)).card := by
  have hsub : K \ E' ⊆ (L \ E) ∪ ((K \ E') ∩ E) := by
    intro e he
    by_cases heE : e ∈ E
    · exact mem_union_right _ (mem_inter.mpr ⟨he,heE⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hKL (mem_sdiff.mp he).1,heE⟩)
  have hc := Finset.card_le_card (Finset.filter_subset_filter (v ∈ ·) hsub)
  rw [Finset.filter_union] at hc
  exact hc.trans (Finset.card_union_le _ _)

/-- The local loss from trimming a dense decomposed reference is at most
one new hole per deleted vertex. No density or hinge hypothesis is used. -/
theorem holes_degree_after_trim (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (W A : Finset V)
    (hD : IsDecomposition H F E D)
    (hDW : ∀ T ∈ D, T ⊆ W) (v : V) :
    SparseEdge.degIn
        (SparseEdge.edges (S07V42.indG H.G (W \ A)) \ keptEdges D (W \ A)) v ≤
      SparseEdge.degIn (SparseEdge.edges (S07V42.indG H.G W) \ E) v + A.card := by
  have hKL : SparseEdge.edges (S07V42.indG H.G (W \ A)) ⊆
      SparseEdge.edges (S07V42.indG H.G W) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hAdj : (S07V42.indG H.G (W \ A)).Adj x y := by
        simpa [SparseEdge.edges] using he
      exact SparseEdge.mem_edges.mpr
        (S07V42.indG_mono H.G Finset.sdiff_subset hAdj)
  exact (holes_degree_le_local _ _ _ _ hKL v).trans
    (Nat.add_le_add_left (loss_degree_le_deleted_card H F E D W A hD hDW v) _)

/-- Direct form for the reference host on the original sampled window.
Here the removed vertices `A` are vertices of that host (typically a subtype
of the ambient vertex type). -/
theorem holes_degree_after_trim_full (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (A : Finset V)
    (hD : IsDecomposition H F E D) (v : V) :
    SparseEdge.degIn
        (SparseEdge.edges (S07V42.indG H.G (univ \ A)) \ keptEdges D (univ \ A)) v ≤
      SparseEdge.degIn (SparseEdge.edges H.G \ E) v + A.card := by
  have hDW : ∀ T ∈ D, T ⊆ (univ : Finset V) := by
    intro T _; exact subset_univ _
  have h := holes_degree_after_trim H F E D univ A hD hDW v
  simpa [S07V42.indG] using h

/-- The nested survivor's actual hole degree is bounded by the old hole
degree plus the number of removed vertices. -/
theorem holes_degree_on_survivors (H : Host V I) (F : Set (Multiset I))
    (E : Finset (Sym2 V)) (D : Finset (Finset V)) (A : Finset V)
    (hD : IsDecomposition H F E D) (v : Survivors A) :
    SparseEdge.degIn
      (edges (restrictedHost H A) \ restrictEdgeSet A (keptEdges D (univ \ A))) v ≤
      SparseEdge.degIn (edges H \ E) v.1 + A.card := by
  let B := SparseEdge.edges (S07V42.indG H.G (univ \ A)) \ keptEdges D (univ \ A)
  have hsub : edges (restrictedHost H A) \
      restrictEdgeSet A (keptEdges D (univ \ A)) ⊆ restrictEdgeSet A B := by
    intro e he
    rcases Finset.mem_sdiff.mp he with ⟨heG,heNot⟩
    apply (mem_restrictEdgeSet A B e).mpr
    apply Finset.mem_sdiff.mpr
    constructor
    · have hG := (mem_edges_restrictedHost H A e).mpr heG
      induction e using Sym2.ind with
      | _ x y =>
        have hp : H.G.Adj x.1 y.1 ∧ x.1 ∉ A ∧ y.1 ∉ A := by
          have hh : (vertexDeleted H A).G.Adj x.1 y.1 := by
            simpa [TypedTriangle.edges] using hG
          exact hh
        have hq : H.G.Adj x.1 y.1 ∧ x.1 ∈ univ \ A ∧ y.1 ∈ univ \ A :=
          ⟨hp.1, by simpa using hp.2.1, by simpa using hp.2.2⟩
        simpa [SparseEdge.edges, S07V42.indG] using hq
    · intro hKeep
      exact heNot ((mem_restrictEdgeSet A (keptEdges D (univ \ A)) e).mpr hKeep)
  have hfirst : SparseEdge.degIn
      (edges (restrictedHost H A) \ restrictEdgeSet A (keptEdges D (univ \ A))) v ≤
      SparseEdge.degIn (restrictEdgeSet A B) v := degree_mono hsub v
  have hsecond : SparseEdge.degIn (restrictEdgeSet A B) v ≤
      SparseEdge.degIn B v.1 := by
    convert Vortex.restricted_edge_load_le A B v using 1
    all_goals
      unfold SparseEdge.degIn
      apply congrArg Finset.card
      ext e
      simp only [Finset.mem_filter]
  exact (hfirst.trans hsecond).trans
    (by simpa only [B, TypedTriangle.edges, SparseEdge.edges] using
      holes_degree_after_trim_full H F E D A hD v.1)

/-- The trimmed dense reference has the same bounded hole degree in the
direct subtype used by the fixed-window child construction. -/
theorem holes_degree_on_direct_trim (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (A : Finset {x // x ∈ W})
    (E : Finset (Sym2 {x // x ∈ W}))
    (D : Finset (Finset {x // x ∈ W}))
    (hD : IsDecomposition
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)
      F E D) :
    letI : DecidableEq {x // x ∈ W} := Classical.decEq _
    let W' := W \ A.image Subtype.val
    let J : Host {x // x ∈ W} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let J' : Host {x // x ∈ W'} I :=
      ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
    let e := nestedToDirectTrim W A
    ∀ v : {x // x ∈ W'},
      SparseEdge.degIn
        (edges J' \ (restrictEdgeSet A (keptEdges D (univ \ A))).image
          (Sym2.map e)) v ≤
        SparseEdge.degIn (edges J \ E) (e.symm v).1 + A.card := by
  let J : Host {x // x ∈ W} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  let W' := W \ A.image Subtype.val
  let J' : Host {x // x ∈ W'} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  let e := nestedToDirectTrim W A
  dsimp only
  intro v
  have hAdj (x y : Survivors A) :
      (restrictedHost J A).G.Adj x y ↔ J'.G.Adj (e x) (e y) := Iff.rfl
  have hEq := holes_degree_equiv e (restrictedHost J A) J'
    (restrictEdgeSet A (keptEdges D (univ \ A))) hAdj (e.symm v)
  have hBound := holes_degree_on_survivors J F E D A hD (e.symm v)
  simp only [e.apply_symm_apply] at hEq
  have hEq' : SparseEdge.degIn
      (edges J' \ (restrictEdgeSet A (keptEdges D (univ \ A))).image
        (Sym2.map e)) v =
      SparseEdge.degIn
        (edges (restrictedHost J A) \ restrictEdgeSet A (keptEdges D (univ \ A)))
        (e.symm v) := by
    convert hEq using 1 <;>
      (congr 1; ext f; simp only [Finset.mem_sdiff, Finset.mem_image, iff_self])
  exact hEq'.le.trans hBound

#print axioms loss_degree_le_deleted_card
#print axioms holes_degree_after_trim
#print axioms holes_degree_after_trim_full

#print axioms decomposition
#print axioms basal
#print axioms holes_degree_le
#print axioms decomposition_on_direct_trim
#print axioms basal_on_direct_trim
#print axioms scheduled_trim_card
#print axioms scheduled_trim_ambient
#print axioms degree_image_equiv
#print axioms degree_mono
#print axioms holes_degree_equiv
#print axioms holes_degree_on_survivors
#print axioms holes_degree_on_direct_trim

end TypedTriangle.ReferenceTrim

