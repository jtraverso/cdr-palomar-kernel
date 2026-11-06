module
public import RequestProject.TypedTriangle.ExplicitUniformCompression
public import RequestProject.TypedTriangle.ExplicitVertexWindows
public import RequestProject.TypedTriangle.NativeCatalogCompression
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative.Explicit

def catalogDimension (β : ℝ) (h : ℕ) : ℕ := (ExplicitSample.compressionSampleSize β h+1)^2
def catalogCoefficient (β : ℝ) (h : ℕ) : ℕ :=
  compD0 (min β 1) (ExplicitSample.compressionSampleSize β h)
def catalogColumn (β : ℝ) (h : ℕ) : ℕ := 3*catalogCoefficient β h
def catalogCompressionOrder (α β : ℝ) (h : ℕ) : ℕ :=
  max (ExplicitSample.compressionOrder β h) (2*ExplicitSample.compressionOrder (α/2) h)

theorem native_all_catalog_compressions_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :

      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (W : Finset V),
        catalogCompressionOrder α β h ≤ W.card → CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        Nonempty (S07V42.CoreCompression H.G H.lab F W (catalogDimension β h) (catalogCoefficient β h) (catalogColumn β h)) ∧
        ∀ Z : Finset V, (Z.card:ℝ) ≤ ExplicitGeometry.deletionBudget α h*W.card →
          Nonempty (S07V42.DelCompression H.G H.lab F Z (catalogDimension (α/2) h) (catalogCoefficient (α/2) h) (catalogColumn (α/2) h)) := by
  let s := ExplicitSample.compressionSampleSize β h
  let D₀ := compD0 (min β 1) s
  let nC := ExplicitSample.compressionOrder β h
  let s' := ExplicitSample.compressionSampleSize (α/2) h
  let D₀' := compD0 (min (α/2) 1) s'
  let nD := ExplicitSample.compressionOrder (α/2) h
  let δ := ExplicitGeometry.deletionBudget α h
  obtain ⟨hδ,hδhalf,hwin⟩ := ExplicitGeometry.deletionBudget_spec hα h
  intro V I _ H F W hn h3 h4 hc3 hc4
  change max nC (2*nD) ≤ W.card at hn

  let K : Host {x // x ∈ W} I := ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  have hcN : nC ≤ Fintype.card {x // x ∈ W} := by
    simpa only [Fintype.card_coe] using (le_max_left _ _).trans hn
  obtain ⟨cc⟩ := ExplicitSample.compression_of_H3H4_explicit β h hβ K F hcN hc3 hc4
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
  obtain ⟨cd⟩ := ExplicitSample.compression_of_H3H4_explicit (α/2) h (by positivity) (restrictedHost H Z) F hnD hg3 hg4
  exact delCompression_of_surviving H F Z cd

#print axioms native_all_catalog_compressions_explicit
end TypedTriangle.CatalogNative.Explicit
