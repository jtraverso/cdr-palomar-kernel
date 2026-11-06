/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexTerminalOuterReserve
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex

/-- One outer rate and one threshold work for every possible intrinsic
index. The rate is fixed before the host reveals which radius it uses. -/
theorem uniform_terminal_absorber_avoiding_outer_core
    (α : ℝ) (h t L : ℕ) (β : Fin (L+1) → ℝ)
    (hα : 0 < α) (hβ : ∀ r, 0 < β r) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1/32 ∧ ∃ K N n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → ∀ r : Fin (L+1),
        Dispersal.PreparedCore H.G H.lab F α h N (β r) →
        ∀ W U : Finset V, (W.card : ℝ) ≤ 2*q*Fintype.card V →
          U.card ≤ t →
          ∃ R : Finset (Sym2 V), Disjoint R (triEdges W) ∧
            R.card ≤ K ∧ (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ M : Finset (Sym2 V), IsPhysical H F M → support M ⊆ U →
              Basal H F (R ∪ M) := by
  have hEach : ∀ r : Fin (L+1), ∃ q : ℝ, 0 < q ∧ q ≤ 1/32 ∧
      ∃ K N n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)), n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h N (β r) →
        ∀ W U : Finset V, (W.card : ℝ) ≤ 2*q*Fintype.card V → U.card ≤ t →
          ∃ R : Finset (Sym2 V), Disjoint R (triEdges W) ∧ R.card ≤ K ∧
            (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ M : Finset (Sym2 V), IsPhysical H F M → support M ⊆ U →
              Basal H F (R ∪ M) := by
    intro r
    exact terminal_absorber_avoiding_outer_core α (β r) h t hα (hβ r)
  choose qr hqr hqrSmall Kr Nr nr hMake using hEach
  have hNonempty : (univ : Finset (Fin (L+1))).Nonempty := ⟨0,mem_univ _⟩
  let q := univ.inf' hNonempty qr
  have hq : 0 < q := (lt_inf'_iff hNonempty).mpr (by intro r _; exact hqr r)
  have hqle : ∀ r, q ≤ qr r := fun r => inf'_le qr (mem_univ r)
  let K := univ.sup Kr
  let N := univ.sup Nr
  let n₀ := univ.sup nr
  have hK : ∀ r, Kr r ≤ K := fun r => le_sup (f := Kr) (mem_univ r)
  have hN : ∀ r, Nr r ≤ N := fun r => le_sup (f := Nr) (mem_univ r)
  have hn₀ : ∀ r, nr r ≤ n₀ := fun r => le_sup (f := nr) (mem_univ r)
  refine ⟨q,hq,(hqle 0).trans (hqrSmall 0),K,N,n₀,?_⟩
  intro V I _ H F hn r Pc W U hW hU
  have Pc' : Dispersal.PreparedCore H.G H.lab F α h (Nr r) (β r) :=
    ⟨Pc.h3,Pc.h4,(fun Z hz => (hN r).trans (Pc.order Z hz)),Pc.lattice_persist⟩
  have hW' : (W.card : ℝ) ≤ 2*qr r*Fintype.card V :=
    hW.trans (by gcongr; exact hqle r)
  obtain ⟨R,hAvoid,hCard,hDeg,hBasal,hAbsorb⟩ :=
    hMake r H F ((hn₀ r).trans hn) Pc' W U hW' hU
  exact ⟨R,hAvoid,hCard.trans (hK r),(fun v => (hDeg v).trans (hK r)),hBasal,hAbsorb⟩

#print axioms uniform_terminal_absorber_avoiding_outer_core
end TypedTriangle.Vortex
