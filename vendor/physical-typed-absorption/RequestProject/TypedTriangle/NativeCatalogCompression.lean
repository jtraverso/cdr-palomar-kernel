/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.DeletedCompressionData
public import RequestProject.TypedTriangle.RestrictedHingeGeometry
public import RequestProject.TypedTriangle.RestrictedVertexBounds
public import RequestProject.S07V42.CompressionAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
variable {V I : Type*} [Fintype V]

lemma indG_complement_eq_vertexDeleted (H : Host V I) (outer : Finset V) :
    S07V42.indG H.G (univ\outer) = (vertexDeleted H outer).G := by
  ext u v
  simp [S07V42.indG,vertexDeleted]

/-- Construct V42's fixed-core compression data from the actual G1-Z export
on the true core subtype. This discharges a named input of the remote return. -/
theorem coreCompression_of_surviving (H : Host V I) (F : Set (Multiset I)) (outer : Finset V)
    {s H₀ D₀ : ℕ} (cmp : Compression (restrictedHost H outer) F s H₀ D₀) :
    Nonempty (S07V42.CoreCompression H.G H.lab F (univ\outer) ((s+1)^2) D₀ (3*D₀)) := by
  obtain ⟨q,hker,hq,S,hS,himg⟩ := surviving_compression_coordinate_data H F outer cmp
  let HC : S07V42.HostCompression (vertexDeleted H outer).G H.lab F ((s+1)^2) D₀ (3*D₀) :=
    ⟨q,hker,hq,S,hS,himg⟩
  have HC' : S07V42.HostCompression (S07V42.indG H.G (univ\outer)) H.lab F
      ((s+1)^2) D₀ (3*D₀) := by
    rw [indG_complement_eq_vertexDeleted]
    exact HC
  exact ⟨⟨HC'.q,HC'.ker_le,HC'.bound,HC'.S,HC'.S_bound,HC'.img⟩⟩

theorem delCompression_of_surviving (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {s H₀ D₀ : ℕ} (cmp : Compression (restrictedHost H Z) F s H₀ D₀) :
    Nonempty (S07V42.DelCompression H.G H.lab F Z ((s+1)^2) D₀ (3*D₀)) := by
  obtain ⟨q,hker,hq,S,hS,himg⟩ := surviving_compression_coordinate_data H F Z cmp
  exact ⟨⟨q,hker,hq,S,hS,himg⟩⟩

/-- Uniform compression family for the fixed core and every small deleted
ambient host. All dimensions, coefficient bounds and the deletion radius precede
the host; neither compression nor a certificate is a premise. -/
theorem native_catalog_compressions (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ d c E d' c' E' : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer : Finset V),
        n₀ ≤ Fintype.card (Survivors outer) →
        CommonNbrCond H F α → HingeCond H F α h →
        CommonNbrCond (restrictedHost H outer) F β → HingeCond (restrictedHost H outer) F β h →
        Nonempty (S07V42.CoreCompression H.G H.lab F (univ\outer) d c E) ∧
        ∀ Z : Finset V, (Z.card:ℝ) ≤ δ*Fintype.card (Survivors outer) →
          Nonempty (S07V42.DelCompression H.G H.lab F Z d' c' E') := by
  obtain ⟨s,H₀,D₀,nC,hC⟩ := compression_of_H3H4 β h hβ
  obtain ⟨s',H₀',D₀',nD,hD⟩ := compression_of_H3H4 (α/2) h (by positivity)
  obtain ⟨δ,hδ,hδhalf,hwin⟩ := original_geometry_vertex_budget hα h
  refine ⟨(s+1)^2,D₀,3*D₀,(s'+1)^2,D₀',3*D₀',δ,hδ,max nC (2*nD),?_⟩
  intro V I _ H F outer hn h3 h4 hc3 hc4
  obtain ⟨cc⟩ := hC (restrictedHost H outer) F ((le_max_left _ _).trans hn) hc3 hc4
  refine ⟨coreCompression_of_surviving H F outer cc,?_⟩
  intro Z hZ
  have hcard : Fintype.card (Survivors outer) ≤ Fintype.card V := Fintype.card_subtype_le _
  have hcardR : (Fintype.card (Survivors outer):ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hZV : (Z.card:ℝ) ≤ δ*Fintype.card V := hZ.trans (mul_le_mul_of_nonneg_left hcardR hδ.le)
  obtain ⟨hZ3,hZ4⟩ := hwin (by positivity) hZV
  obtain ⟨hg3,hg4⟩ := original_geometry_restrictedHost hα.le h3 h4 Z hZ3 hZ4
  have hhalf : (Z.card:ℝ) ≤ (Fintype.card V:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hδhalf (by positivity : (0:ℝ) ≤ Fintype.card V)
    nlinarith
  have hcZ := card_survivors_add_card Z
  have hcZR : (Fintype.card (Survivors Z):ℝ)+Z.card = Fintype.card V := by exact_mod_cast hcZ
  have hlarge : (2*nD:ℕ) ≤ Fintype.card V := ((le_max_right _ _).trans hn).trans hcard
  have hnD : nD ≤ Fintype.card (Survivors Z) := by
    have hh : (2:ℝ)*nD ≤ Fintype.card V := by exact_mod_cast hlarge
    exact_mod_cast (by linarith : (nD:ℝ) ≤ Fintype.card (Survivors Z))
  obtain ⟨cd⟩ := hD (restrictedHost H Z) F hnD hg3 hg4
  exact delCompression_of_surviving H F Z cd
/-- The same native compression export for an arbitrary actual core W. Its
geometry is tested on the membership subtype, matching the macro-bank API. -/
theorem native_all_catalog_compressions (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ d c E d' c' E' : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        n₀ ≤ W.card → CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        Nonempty (S07V42.CoreCompression H.G H.lab F W d c E) ∧
        ∀ Z : Finset V, (Z.card:ℝ) ≤ δ*W.card →
          Nonempty (S07V42.DelCompression H.G H.lab F Z d' c' E') := by
  obtain ⟨s,H₀,D₀,nC,hC⟩ := compression_of_H3H4 β h hβ
  obtain ⟨s',H₀',D₀',nD,hD⟩ := compression_of_H3H4 (α/2) h (by positivity)
  obtain ⟨δ,hδ,hδhalf,hwin⟩ := original_geometry_vertex_budget hα h
  refine ⟨(s+1)^2,D₀,3*D₀,(s'+1)^2,D₀',3*D₀',δ,hδ,max nC (2*nD),?_⟩
  intro V I _ H F W hn h3 h4 hc3 hc4
  let K : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hcN : nC ≤ Fintype.card {x // x ∈ W} := by
    simpa only [Fintype.card_coe] using (le_max_left _ _).trans hn
  obtain ⟨cc⟩ := hC K F hcN hc3 hc4
  obtain ⟨q,hker,hq,S,hS,himg⟩ := compression_local_coordinate_data K F cc
  let HC : S07V42.HostCompression K.G K.lab F ((s+1)^2) D₀ (3*D₀) :=
    ⟨q,hker,hq,S,hS,himg⟩
  refine ⟨⟨S07V42.CoreCompression.ofSubtype HC⟩,?_⟩
  intro Z hZ
  have hcard : W.card ≤ Fintype.card V := card_le_univ W
  have hcardR : (W.card:ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hZV : (Z.card:ℝ) ≤ δ*Fintype.card V :=
    hZ.trans (mul_le_mul_of_nonneg_left hcardR hδ.le)
  obtain ⟨hZ3,hZ4⟩ := hwin (by positivity) hZV
  obtain ⟨hg3,hg4⟩ := original_geometry_restrictedHost hα.le h3 h4 Z hZ3 hZ4
  have hhalf : (Z.card:ℝ) ≤ (Fintype.card V:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hδhalf (by positivity : (0:ℝ) ≤ Fintype.card V)
    nlinarith
  have hcZ := card_survivors_add_card Z
  have hcZR : (Fintype.card (Survivors Z):ℝ)+Z.card = Fintype.card V := by exact_mod_cast hcZ
  have hlarge : (2*nD:ℕ) ≤ Fintype.card V := ((le_max_right _ _).trans hn).trans hcard
  have hnD : nD ≤ Fintype.card (Survivors Z) := by
    have hh : (2:ℝ)*nD ≤ Fintype.card V := by exact_mod_cast hlarge
    exact_mod_cast (by linarith : (nD:ℝ) ≤ Fintype.card (Survivors Z))
  obtain ⟨cd⟩ := hD (restrictedHost H Z) F hnD hg3 hg4
  exact delCompression_of_surviving H F Z cd
end TypedTriangle.CatalogNative
