/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexNestedH4Transport
public import RequestProject.S07V42.CompressionAdapter
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- Pulling a physical circulation through an exact relabelling remains
physical. This is the reticular counterpart of the H3/H4 transport. -/
theorem lattice_pull_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I))
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (y : Sym2 W → ℤ) (hy : y ∈ SparseEdge.lattice H₂.G H₂.lab F) :
    (fun f => y (Sym2.map e f)) ∈ SparseEdge.lattice H₁.G H₁.lab F := by
  have hG : H₁.G = H₂.G.comap e := by
    apply SimpleGraph.ext
    funext x z
    apply propext
    exact hAdj x z
  have hL : H₁.lab = H₂.lab ∘ e := by
    funext x
    exact hLab x
  have hEdges : S07V42.EdgesIn H₂.G e := by
    intro a b _
    exact ⟨e.symm a,e.apply_symm_apply a⟩
  have hh := S07V42.pull_lattice e.injective hEdges
    (G := H₂.G) (lab := H₂.lab) (F := F) hy
  change (fun f => y (Sym2.map e f)) ∈
    SparseEdge.lattice (H₂.G.comap e) (H₂.lab ∘ e) F at hh
  rw [hG,hL]
  exact hh

/-- Deleting corresponding vertex sets commutes with an exact relabelling. -/
def deletedWindowEquiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (Z : Finset V) :
    Dispersal.Surv Z ≃ Dispersal.Surv (Z.image e) where
  toFun x := ⟨e x.1, by
    intro hx
    obtain ⟨z,hz,hez⟩ := Finset.mem_image.mp hx
    exact x.2 (e.injective hez ▸ hz)⟩
  invFun y := ⟨e.symm y.1, by
    intro hy
    exact y.2 (Finset.mem_image.mpr ⟨e.symm y.1,hy,e.apply_symm_apply y.1⟩)⟩
  left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv := by intro y; apply Subtype.ext; exact e.apply_symm_apply y.1

/-- The edge-vector restriction square commutes on every remaining edge.
This identity is needed to transport `PreparedCore.lattice_persist`. -/
theorem restr_pull_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (Z : Finset V) (y : Sym2 W → ℤ)
    (f : Sym2 (Dispersal.Surv Z)) :
    Dispersal.restr Z (fun g => y (Sym2.map e g)) f =
      Dispersal.restr (Z.image e) y
        (Sym2.map (deletedWindowEquiv e Z) f) := by
  induction f using Sym2.ind with
  | _ a b => rfl

/-- The full prepared-core contract is invariant under an exact relabelling
of vertices, including the integer-lattice persistence after every further
small vertex deletion. -/
theorem preparedCore_equiv {V W I : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (H₁ : Host V I) (H₂ : Host W I)
    (F : Set (Multiset I)) (α : ℝ) (h N : ℕ) (β : ℝ)
    (hAdj : ∀ x y, H₁.G.Adj x y ↔ H₂.G.Adj (e x) (e y))
    (hLab : ∀ x, H₁.lab x = H₂.lab (e x))
    (P : Dispersal.PreparedCore H₁.G H₁.lab F α h N β) :
    Dispersal.PreparedCore H₂.G H₂.lab F α h N β := by
  have hCard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hZeq (Z' : Finset W) : (Z'.image e.symm).image e = Z' := by
    ext w
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v,⟨w',hw',rfl⟩,rfl⟩
      simpa using hw'
    · intro hw
      exact ⟨e.symm w,⟨w,hw,rfl⟩,e.apply_symm_apply w⟩
  have hBudget (Z' : Finset W) (hz : (Z'.card : ℝ) ≤ β * Fintype.card W) :
      (((Z'.image e.symm).card : ℕ) : ℝ) ≤ β * Fintype.card V := by
    rw [Finset.card_image_of_injective Z' e.symm.injective,hCard]
    exact hz
  have hDelAdj (Z : Finset V) (x y : Dispersal.Surv Z) :
      (Dispersal.subG H₁.G Z).Adj x y ↔
        (Dispersal.subG H₂.G (Z.image e)).Adj
          (deletedWindowEquiv e Z x) (deletedWindowEquiv e Z y) :=
    hAdj x.1 y.1
  have hDelLab (Z : Finset V) (x : Dispersal.Surv Z) :
      Dispersal.subLab H₁.lab Z x =
        Dispersal.subLab H₂.lab (Z.image e) (deletedWindowEquiv e Z x) :=
    hLab x.1
  refine ⟨?_,?_,?_,?_⟩
  · intro Z' hz'
    let Z := Z'.image e.symm
    have hh := commonNbrCond_equiv (deletedWindowEquiv e Z)
      (⟨Dispersal.subG H₁.G Z,Dispersal.subLab H₁.lab Z⟩ : Host _ I)
      (⟨Dispersal.subG H₂.G (Z.image e),Dispersal.subLab H₂.lab (Z.image e)⟩ : Host _ I)
      F α (hDelAdj Z) (hDelLab Z) (P.h3 Z (hBudget Z' hz'))
    dsimp only [Z] at hh
    rw [hZeq Z'] at hh
    exact hh
  · intro Z' hz'
    let Z := Z'.image e.symm
    have hh := hingeCond_equiv (deletedWindowEquiv e Z)
      (⟨Dispersal.subG H₁.G Z,Dispersal.subLab H₁.lab Z⟩ : Host _ I)
      (⟨Dispersal.subG H₂.G (Z.image e),Dispersal.subLab H₂.lab (Z.image e)⟩ : Host _ I)
      F α h (hDelAdj Z) (hDelLab Z) (P.h4 Z (hBudget Z' hz'))
    dsimp only [Z] at hh
    rw [hZeq Z'] at hh
    exact hh
  · intro Z' hz'
    let Z := Z'.image e.symm
    have hh := P.order Z (hBudget Z' hz')
    have hc : Fintype.card (Dispersal.Surv Z) =
        Fintype.card (Dispersal.Surv (Z.image e)) :=
      Fintype.card_congr (deletedWindowEquiv e Z)
    rw [hc,hZeq Z'] at hh
    exact hh
  · intro Z' hz' y hy hyvan
    let Z := Z'.image e.symm
    let eZ := deletedWindowEquiv e Z
    have hy₁ := lattice_pull_equiv e H₁ H₂ F hAdj hLab y hy
    have hvan₁ : ∀ f : Sym2 V, (∃ z ∈ Z, z ∈ f) →
        (fun g => y (Sym2.map e g)) f = 0 := by
      intro f ⟨z,hz,hzf⟩
      have hz' : e z ∈ Z' := by
        rw [← hZeq Z']
        exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
      have hzf' : e z ∈ Sym2.map e f :=
        Sym2.mem_map.mpr ⟨z,hzf,rfl⟩
      exact hyvan (Sym2.map e f) ⟨e z,hz',hzf'⟩
    have hy₁' := P.lattice_persist Z (hBudget Z' hz')
      (fun g => y (Sym2.map e g)) hy₁ hvan₁
    let K₁ : Host (Dispersal.Surv Z) I :=
      ⟨Dispersal.subG H₁.G Z,Dispersal.subLab H₁.lab Z⟩
    let K₂ : Host (Dispersal.Surv (Z.image e)) I :=
      ⟨Dispersal.subG H₂.G (Z.image e),Dispersal.subLab H₂.lab (Z.image e)⟩
    have hAdjBack (a b : Dispersal.Surv (Z.image e)) :
        K₂.G.Adj a b ↔ K₁.G.Adj (eZ.symm a) (eZ.symm b) := by
      simpa [K₁,K₂,eZ] using (hDelAdj Z (eZ.symm a) (eZ.symm b)).symm
    have hLabBack (a : Dispersal.Surv (Z.image e)) :
        K₂.lab a = K₁.lab (eZ.symm a) := by
      simpa [K₁,K₂,eZ] using (hDelLab Z (eZ.symm a)).symm
    have hy₂ := lattice_pull_equiv eZ.symm K₂ K₁ F hAdjBack hLabBack
      (Dispersal.restr Z (fun g => y (Sym2.map e g))) hy₁'
    have hRestr :
        (fun f => (Dispersal.restr Z (fun g => y (Sym2.map e g)))
          (Sym2.map eZ.symm f)) =
        Dispersal.restr (Z.image e) y := by
      funext f
      have hh := restr_pull_equiv e Z y (Sym2.map eZ.symm f)
      have hinv : Sym2.map eZ (Sym2.map eZ.symm f) = f := by
        induction f using Sym2.ind with
        | _ a b => simp [Sym2.map_mk]
      change (Dispersal.restr Z (fun g => y (Sym2.map e g)))
        (Sym2.map eZ.symm f) =
          Dispersal.restr (Z.image e) y
            (Sym2.map eZ (Sym2.map eZ.symm f)) at hh
      rw [hinv] at hh
      exact hh
    rw [hRestr] at hy₂
    dsimp only [K₂,Z] at hy₂
    rw [hZeq Z'] at hy₂
    exact hy₂

/-- The prepared lattice core produced after trimming a sampled host lives
on the direct membership subtype of the final sampled window. -/
theorem nested_preparedCore_direct {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (A : Finset (Survivors (univ \ W)))
    (α : ℝ) (h N : ℕ) (β : ℝ)
    (P : Dispersal.PreparedCore
      (restrictedHost (restrictedHost H (univ \ W)) A).G
      (restrictedHost (restrictedHost H (univ \ W)) A).lab
      F α h N β) :
    Dispersal.PreparedCore
      (H.G.comap (Subtype.val : {v : V // v ∈ W \ liftVertexSet (univ \ W) A} → V))
      (H.lab ∘ Subtype.val) F α h N β := by
  let e := nestedToDirectWindowEquiv W A
  let H' : Host {v : V // v ∈ W \ liftVertexSet (univ \ W) A} I :=
    ⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩
  exact preparedCore_equiv e
    (restrictedHost (restrictedHost H (univ \ W)) A) H' F α h N β
    (fun _ _ => Iff.rfl) (fun _ => rfl) P

#print axioms lattice_pull_equiv
#print axioms restr_pull_equiv
#print axioms preparedCore_equiv
#print axioms nested_preparedCore_direct

end TypedTriangle.Vortex
