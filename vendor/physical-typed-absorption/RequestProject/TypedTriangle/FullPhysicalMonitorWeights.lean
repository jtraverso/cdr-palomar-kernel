/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V46.FullMonitor
public import RequestProject.S07V38.BoundedExtension
public import RequestProject.TypedTriangle.NativeCoreMonitorRepresentation
public import RequestProject.TypedTriangle.ResidualMonitorBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V44 S07V46
variable {V I : Type*} [Fintype V] {H : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)} {W : Finset V} {d c E : ℕ}

/-- The full monitor need not annihilate ambient physical triangles. A bounded
extension from the actual core profile gives its global edge weights directly,
with a bound fixed before the host. No fictitious ambient annihilation or
surjectivity of the coordinate map is assumed. -/
theorem full_physical_monitor_weights {R A M K : ℕ}
    (C0 : CoreCompression H lab F W d c E) (Fm : FullMonitor C0 R A M K) :
    ∃ lam : Fin K → Sym2 V → ℝ,
      (∀ j e, |lam j e| ≤ (M*(d*c):ℕ)) ∧
      ∀ j (x : MCore H lab F W), ∑ e, lam j e*((x.1 e:ℤ):ℝ) =
        physMonReal C0 ∅ Fm.psi j x := by
  have hEach : ∀ j : Fin K, ∃ lam : Sym2 V → ℝ,
      (∀ e, |lam e| ≤ (M*(d*c):ℕ)) ∧
      ∀ x : MCore H lab F W, ∑ e, lam e*((x.1 e:ℤ):ℝ) =
        physMonReal C0 ∅ Fm.psi j x := by
    intro j
    apply S07V38.bounded_extension (MCore H lab F W) (physMonReal C0 ∅ Fm.psi j) (by positivity)
    intro x
    rw [CoreMonitor.real_l1E_eq]
    exact physMonReal_abs_le C0 ∅ Fm.psi (one_le_monR R E) Fm.box_le j x
  choose lam hb hr using hEach
  exact ⟨lam,hb,hr⟩

/-- Pairings with the actual full-monitor weights bound its INTEGER norm.
The quotient and its torsion are unchanged by this real-valued estimate. -/
theorem full_monitor_norm_of_edge_moments {R A M K : ℕ}
    (C0 : CoreCompression H lab F W d c E) (Fm : FullMonitor C0 R A M K)
    (x : MCore H lab F W) (J : Finset (Sym2 V)) (hx : (x : Sym2 V → ℤ) = ind J)
    (lam : Fin K → Sym2 V → ℝ)
    (hrep : ∀ j, ∑ e, lam j e*((x.1 e:ℤ):ℝ) = physMonReal C0 ∅ Fm.psi j x)
    (B : ℝ) (hmom : ∀ j, |LocalizedCover.edgeSum (lam j) J| ≤ B) :
    (S07V32.l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤ K*B := by
  have heach : ∀ j : Fin K, |((physMon C0 ∅ Fm.psi x j : ℤ):ℝ)| ≤ B := by
    intro j
    rw [←physMonReal_apply,←hrep j]
    simpa only [hx,pairing_integer_indicator] using hmom j
  calc
    (S07V32.l1 (physMon C0 ∅ Fm.psi x) : ℝ) =
        ∑ j : Fin K, |((physMon C0 ∅ Fm.psi x j : ℤ):ℝ)| := by simp [S07V32.l1]
    _ ≤ ∑ _j : Fin K, B := sum_le_sum (fun j _ => heach j)
    _ = K*B := by simp

/-- The full monitor also pays the actual stock contribution. The stock is
not removed from the final residue by an invalid annihilation argument. -/
theorem stock_full_monitor_bound (HH : Host V I)
    (D : Finset (Finset V)) (hD : IsDecomposition HH F (BasalIncidence.cover D) D)
    {C0 : CoreCompression HH.G HH.lab F W d c E} {R A M K : ℕ}
    (Fm : FullMonitor C0 R A M K) (x : MCore HH.G HH.lab F W)
    (J : Finset (Sym2 V)) (hx : (x : Sym2 V → ℤ) = ind J)
    (lam : Fin K → Sym2 V → ℝ)
    (hrep : ∀ j, ∑ e, lam j e*((x.1 e:ℤ):ℝ) = physMonReal C0 ∅ Fm.psi j x)
    (L DX DC E0 : ℝ) (hL : 0 ≤ L)
    (hstock : ∀ v, (((BasalIncidence.cover D).filter (fun e => v ∈ e)).card : ℝ) ≤ DX)
    (htri : ∀ j T, IsAllowed HH F T → |LocalizedCover.triSum (lam j) T| ≤ 3*L*T.card)
    (hleft : ∀ j, |LocalizedCover.edgeSum (lam j) J-
      LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D)| ≤
        E0+(3*L*Fintype.card V)*DC/2) :
    (S07V32.l1 (physMon C0 ∅ Fm.psi x) : ℝ) ≤
      K*(E0+(3*L*Fintype.card V)*(DC+DX)/2) := by
  have hstock' : ∀ j, |LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D)| ≤
      (3*L*Fintype.card V)*DX/2 := by
    intro j
    have hb := LocalizedCover.packing_localized_bound
      (show IsPacking HH F D from ⟨hD.1,hD.2.1⟩) DX L hL
      (by simpa only [hD.2.2] using hstock) univ (lam j)
      (fun T hT => by simpa using htri j T hT)
    rw [←LocalizedCover.packing_edge_sum_eq
      (show IsPacking HH F D from ⟨hD.1,hD.2.1⟩),hD.2.2] at hb
    simpa using hb
  apply full_monitor_norm_of_edge_moments C0 Fm x J hx lam hrep
  intro j
  have hh := abs_add_le
    (LocalizedCover.edgeSum (lam j) J-LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D))
    (LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D))
  have hh' := hh.trans (add_le_add (hleft j) (hstock' j))
  simpa only [sub_add_cancel] using (show
    |LocalizedCover.edgeSum (lam j) J-LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D)+
      LocalizedCover.edgeSum (lam j) (BasalIncidence.cover D)| ≤
        E0+(3*L*Fintype.card V)*(DC+DX)/2 by nlinarith only [hh'])

end TypedTriangle.CatalogNative
