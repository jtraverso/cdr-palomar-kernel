/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPreservedWindowEquiv
public import RequestProject.TypedTriangle.VortexDiffuseSeedEquiv
public import RequestProject.TypedTriangle.VortexCleanHingeEquiv
public import RequestProject.TypedTriangle.VortexPhysicalEmbedding
public import RequestProject.TypedTriangle.VortexReferenceTrim
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- Pull a paid child to the literal nested survivor carrier. -/
def pullEquivHost {X Y I : Type} (e : X ≃ Y) (J : Host Y I) : Host X I :=
  ⟨J.G.comap e,J.lab ∘ e⟩

theorem edges_image_equiv {X Y I : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (H : Host X I) (J : Host Y I)
    (hAdj : ∀u v, H.G.Adj u v ↔ J.G.Adj (e u) (e v)) :
    (edges H).image (Sym2.map e) = edges J := by
  ext f
  constructor
  · intro hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    induction g using Sym2.ind with
    | _ u v =>
      have huv : H.G.Adj u v := by simpa [edges] using hg
      simpa [edges] using (hAdj u v).1 huv
  · intro hf
    let g := Sym2.map e.symm f
    have hfg : Sym2.map e g = f := by
      induction f using Sym2.ind with
      | _ u v => simp [g]
    refine mem_image.mpr ⟨g,?_,hfg⟩
    induction f using Sym2.ind with
    | _ u v =>
      have huv : J.G.Adj u v := by simpa [edges] using hf
      have hRaw := (hAdj (e.symm u) (e.symm v)).2 (by simpa using huv)
      simpa [g,edges] using hRaw

/-- H1, physicality, H3 and clean H4 are transported together, with the
same coefficient constant, same density and same hinge order. -/
theorem paid_child_pull_equiv {X Y I : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (J : Host Y I) (F : Set (Multiset I))
    (C α : ℝ) (h : ℕ) (ψ : Finset Y → ℝ)
    (hSeed : IsDiffuseSeed J F C ψ) (hPhys : IsPhysical J F (edges J))
    (h3 : CommonNbrCond J F α) (hClean : CleanHingeCond J F α h) :
    IsDiffuseSeed (pullEquivHost e J) F C (equivSeed e ψ) ∧
    IsPhysical (pullEquivHost e J) F (edges (pullEquivHost e J)) ∧
    CommonNbrCond (pullEquivHost e J) F α ∧
    CleanHingeCond (pullEquivHost e J) F α h := by
  have hAdj : ∀u v, (pullEquivHost e J).G.Adj u v ↔ J.G.Adj (e u) (e v) :=
    fun _ _ => Iff.rfl
  have hLab : ∀u, (pullEquivHost e J).lab u = J.lab (e u) := fun _ => rfl
  have hAdjInv : ∀u v, J.G.Adj u v ↔
      (pullEquivHost e J).G.Adj (e.symm u) (e.symm v) := by
    intro u v
    change J.G.Adj u v ↔ J.G.Adj (e (e.symm u)) (e (e.symm v))
    simp only [e.apply_symm_apply]
  have hLabInv : ∀u, J.lab u = (pullEquivHost e J).lab (e.symm u) := by
    intro u
    change J.lab u = J.lab (e (e.symm u))
    rw [e.apply_symm_apply]
  refine ⟨diffuse_seed_pull_equiv e _ J F C hAdj hLab ψ hSeed,?_,
    commonNbrCond_equiv e.symm J _ F α hAdjInv hLabInv h3,
    cleanHingeCond_equiv e.symm J _ F α h hAdjInv hLabInv hClean⟩
  have hp := physical_embedding J (pullEquivHost e J) F e.symm.toEmbedding
    (fun u v huv => (hAdjInv u v).1 huv) hLabInv hPhys
  have he := edges_image_equiv e.symm J (pullEquivHost e J) hAdjInv
  change IsPhysical _ _ ((edges J).image (Sym2.map e.symm)) at hp
  rw [he] at hp
  exact hp

/-- The uniform paid-hole bound is unchanged by the child carrier bridge. -/
theorem paid_child_holes_pull_equiv {X Y I : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (Hraw : Host X I) (Jraw Jchild : Host Y I) (ζ : ℝ)
    (hAdj : ∀u v, Hraw.G.Adj u v ↔ Jraw.G.Adj (e u) (e v))
    (hHole : ∀v, (SparseEdge.degIn (edges Jraw \ edges Jchild) v : ℝ) ≤
      ζ*Fintype.card Y) :
    ∀v, (SparseEdge.degIn (edges Hraw \ edges (pullEquivHost e Jchild)) v : ℝ) ≤
      ζ*Fintype.card X := by
  have hEdges := edges_image_equiv e (pullEquivHost e Jchild) Jchild (fun _ _ => Iff.rfl)
  intro v
  have heq := ReferenceTrim.holes_degree_equiv e Hraw Jraw
    (edges (pullEquivHost e Jchild)) hAdj v
  rw [hEdges] at heq
  have hh := hHole (e v)
  rw [heq,← Fintype.card_congr e] at hh
  exact hh

#print axioms paid_child_pull_equiv
#print axioms paid_child_holes_pull_equiv
end TypedTriangle.Vortex
