/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalPackingIncidence
public import RequestProject.TypedTriangle.NativeSeedNibble
public import RequestProject.TypedTriangle.CoreForkBridge
public import RequestProject.TypedTriangle.SeedPositivity
public import RequestProject.TypedTriangle.CertBoundary
public import RequestProject.TypedTriangle.CompositeHinge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A basal reserve constructed from the original H1 and H3. The reserve
is a real subpacking, with linear supply of permitted completion wings at
every physical edge. This is not a refiner or an absorber-capacity theorem. -/

noncomputable section
open Finset Classical
namespace TypedTriangle.BasalIncidence
variable {V I : Type*} [Fintype V]

theorem good_supply {H : Host V I} {F : Set (Multiset I)} {α δ : ℝ}
    (hH3 : CommonNbrCond H F α) (P : Finset (Finset V))
    (hdeg : ∀ x, (((edges H \ cover P).filter (fun e => x ∈ e)).card : ℝ) ≤
      δ * Fintype.card V) {u v a : V} (hTa : IsAllowed H F {u,v,a}) :
    (α - 2 * δ) * Fintype.card V ≤ (good H F P u v).card := by
  obtain ⟨huv,hua,hva⟩ := distinct_of_card_three hTa.1
  have htype : ({H.lab u,H.lab v,H.lab a} : Multiset I) ∈ F := by
    have ht := hTa.2.2
    rwa [Finset.insert_val_of_notMem (by simp [huv,hua]),
      Finset.insert_val_of_notMem (by simp [hva])] at ht
  have hfull := hH3 u v huv (H.lab a) htype
  let B := edges H \ cover P
  let bad := SparseEdge.nbrIn B u ∪ SparseEdge.nbrIn B v
  have hbad : (bad.card : ℝ) ≤ 2 * δ * Fintype.card V := by
    have hu0 : ((SparseEdge.nbrIn B u).card : ℝ) ≤
        ((B.filter (fun e => u ∈ e)).card : ℝ) := by
      exact_mod_cast SparseEdge.card_nbrIn_le B u
    have hv0 : ((SparseEdge.nbrIn B v).card : ℝ) ≤
        ((B.filter (fun e => v ∈ e)).card : ℝ) := by
      exact_mod_cast SparseEdge.card_nbrIn_le B v
    have hu : ((SparseEdge.nbrIn B u).card : ℝ) ≤ δ * Fintype.card V :=
      hu0.trans (hdeg u)
    have hv : ((SparseEdge.nbrIn B v).card : ℝ) ≤ δ * Fintype.card V :=
      hv0.trans (hdeg v)
    have hb : (bad.card : ℝ) ≤ (SparseEdge.nbrIn B u).card +
        (SparseEdge.nbrIn B v).card := by exact_mod_cast card_union_le _ _
    linarith
  have hcover : commonNbrs H (H.lab a) u v ⊆ good H F P u v ∪ bad := by
    intro w hw
    have ht := allowed_of_commonNbr hTa hw
    have hw' := (mem_filter.mp hw).2
    by_cases hu : s(u,w) ∈ cover P
    · by_cases hv : s(v,w) ∈ cover P
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ht,hu,hv⟩)
      · have he : s(v,w) ∈ B := mem_sdiff.mpr ⟨by simpa [edges] using hw'.2.1,hv⟩
        exact mem_union_right _ (mem_union_right _ (by simp [SparseEdge.nbrIn,he]))
    · have he : s(u,w) ∈ B := mem_sdiff.mpr ⟨by simpa [edges] using hw'.1,hu⟩
      exact mem_union_right _ (mem_union_left _ (by simp [SparseEdge.nbrIn,he]))
  have hcard : ((commonNbrs H (H.lab a) u v).card : ℝ) ≤
      (good H F P u v).card + bad.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  nlinarith

theorem edge_allowed_of_seed {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {φ : Finset V → ℝ} (hC : 0 < C) (hH1 : IsDiffuseSeed H F C φ)
    {u v : V} (huv : H.G.Adj u v) : ∃ a, IsAllowed H F {u,v,a} := by
  obtain ⟨T,hT,he⟩ := (CoreForkBridge.diffuse_to_fork hC hH1).edgeCovered s(u,v)
    (by simpa [SparseEdge.edges] using huv)
  obtain ⟨a,ha⟩ := eq_insert_of_mem_triEdges hT.1 he
  refine ⟨a,?_⟩
  rwa [tri_eq_insert_toFinset,← ha]

/-- Construct the basal reserve from H1 and H3 alone. All constants precede
the host; the completion guarantee holds at every actual host edge. -/
theorem reserve_of_H1H3 (C α ρ : ℝ) (hC : 1 ≤ C) (hα : 0 < α) (hρ : 0 < ρ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] (I : Type) (H : Host V I) (F : Set (Multiset I))
        (φ : Finset V → ℝ), n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        CommonNbrCond H F α →
        ∃ D : Finset (Finset V), IsDecomposition H F (cover D) D ∧
          (∀ x, (((cover D).filter (fun e => x ∈ e)).card : ℝ) < ρ * Fintype.card V) ∧
          ∀ u v, H.G.Adj u v → κ * Fintype.card V ≤ (good H F D u v).card := by
  let δ := min (α / 4) (1 / 2)
  let q := min (ρ / 12) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  obtain ⟨nP,hP⟩ := NativeNibble.packing_of_diffuse_seed C δ hC hδ
    ((min_le_right _ _).trans (by norm_num))
  obtain ⟨nS,hS⟩ := sample_packing q (α / 2) hq
    ((min_le_right _ _).trans (by norm_num)) (by positivity)
  refine ⟨α / 2 * q ^ 2 / 2, by positivity, max nP nS, ?_⟩
  intro V _ I H F φ hn hH1 hH3
  obtain ⟨P,_,hPack,hDeg⟩ := hP H F φ ((le_max_left _ _).trans hn) hH1
  let τ := {uv : V × V // H.G.Adj uv.1 uv.2}
  let u : τ → V := fun t => t.val.1
  let v : τ → V := fun t => t.val.2
  have hτ : Fintype.card τ ≤ Fintype.card V ^ 2 := by
    calc
      Fintype.card τ ≤ Fintype.card (V × V) := Fintype.card_subtype_le _
      _ = _ := by rw [Fintype.card_prod]; ring
  have hSupply : ∀ t : τ, α / 2 * Fintype.card V ≤ (good H F P (u t) (v t)).card := by
    intro t
    obtain ⟨a,ha⟩ := edge_allowed_of_seed (by linarith : 0 < C) hH1 t.property
    have hh := good_supply hH3 P hDeg ha
    have hδa : δ ≤ α / 4 := min_le_left _ _
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith
  obtain ⟨D,_,hD,hSmall,hGood⟩ := hS V I H F P hPack ((le_max_right _ _).trans hn)
    τ u v hτ hSupply
  refine ⟨D,hD,?_,?_⟩
  · intro x
    have hqρ : q ≤ ρ / 12 := min_le_left _ _
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hx := hSmall x
    nlinarith
  · intro x y hxy
    have hh := hGood ⟨(x,y),hxy⟩
    dsimp only [u,v] at hh
    nlinarith

end TypedTriangle.BasalIncidence
