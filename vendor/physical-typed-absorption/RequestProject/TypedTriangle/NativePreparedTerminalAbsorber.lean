/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PreparedUniformSupply
public import RequestProject.S07V31.TerminalAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.PreparedSupply

/-- Reserve the universal terminal absorber directly in the already
prepared host. No second vertex deletion is made after choosing that host;
the terminal set and forbidden edges precede the eventual residue. -/
theorem terminal_absorber_on_prepared_host (α β : ℝ) (h t : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K N n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h N β →
        ∀ (U : Finset V) (B : Finset (Sym2 V)) (b : ℕ),
          U.card ≤ t → (∀ v, degIn B v ≤ b) →
          (b : ℝ) ≤ ε * Fintype.card V →
          ∃ R : Finset (Sym2 V),
            Disjoint R B ∧ Disjoint R (triEdges U) ∧ R.card ≤ K ∧
            (∀ v, degIn R v ≤ K) ∧ Basal H F R ∧
            ∀ L : Finset (Sym2 V), IsPhysical H F L → support L ⊆ U →
              Basal H F (R ∪ L) := by
  obtain ⟨N,s,hSupply⟩ := prepared_uniform_supply α h (t*t) hα
  obtain ⟨δ,hδ,nSupply,hS⟩ := hSupply β hβ
  obtain ⟨ε,hε,nTerminal,hTerminal⟩ := S07V31.universal_terminal_absorber t s hδ
  refine ⟨ε,hε,s*2^(t*t),N,max nSupply nTerminal,?_⟩
  intro V I _ H F hn Pc U B b hU hB hb
  have hsup : S07V31.TerminalSupply H.G H.lab F U s
      ⌊δ * Fintype.card V⌋₊ ⌊δ * Fintype.card V⌋₊ := by
    intro P hP _
    obtain ⟨hPE,hPhys⟩ := S07V31.mem_physSubsets.mp hP
    have hCard : P.card ≤ t*t :=
      (card_le_card hPE).trans ((S07V31.card_triEdges_le U).trans
        (Nat.mul_le_mul hU hU))
    exact hS H F ((le_max_left _ _).trans hn) Pc P hCard hPhys
  exact hTerminal H.G H.lab F U B b ((le_max_right _ _).trans hn) hU hB hb hsup

#print axioms terminal_absorber_on_prepared_host
end TypedTriangle.PreparedSupply
