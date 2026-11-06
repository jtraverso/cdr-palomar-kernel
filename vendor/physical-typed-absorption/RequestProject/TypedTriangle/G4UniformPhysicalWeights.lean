/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LocalizedCatalogMonitors
public import RequestProject.TypedTriangle.NativeCoreMonitorRepresentation
public import RequestProject.TypedTriangle.FullPhysicalMonitorWeights
public import RequestProject.TypedTriangle.SeedMoment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A single triangle-quota constant for every coordinate of both the
localized physical monitors and the full monitor. The catalog dimensions
precede the host, so this constant can precede the monitored nibble. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open S07V42 S07V44 S07V46 TypedTriangle.LocalizedCover

theorem uniform_physical_monitor_weights (α β : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ L : ℝ, 0 < L ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (outer bad : Finset V)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
        (Fm : FullMonitor C0 R A M K),
        n₀ ≤ Fintype.card (Survivors bad) →
        n₀ ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α →
        HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β →
        HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β →
        HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤
          S07V37.delOf β h * Fintype.card (Survivors outer) →
        ∃ loc full : Fin K → Sym2 V → ℝ,
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ j T, IsAllowed H F T →
            |triSum (loc j) T| ≤ 3 * L * (T∩bad).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * L * T.card := by
  obtain ⟨B, hB, n₀, hlocal⟩ := physical_monitors_localize α β h hα hβ
  let D : ℝ := (M * (d * c) : ℕ)
  let L : ℝ := max (S07V39.glueConst β (B * D)) D + 1
  have hL : 0 < L := by
    dsimp [L]
    have hD : 0 ≤ D := Nat.cast_nonneg _
    linarith [le_max_right (S07V39.glueConst β (B * D)) D]
  refine ⟨L, hL, n₀, ?_⟩
  intro V I _ H F outer bad C0 Mon Fm hnBad hnBoth hBad3 hBad4 hJoint3 hJoint4
    hCore3 hCore4 hSmall
  obtain ⟨loc, hlocBound, hlocRep, _, hlocTri⟩ :=
    hlocal H F outer bad hnBad hnBoth hBad3 hBad4 hJoint3 hJoint4
      hCore3 hCore4 hSmall C0 Mon
  obtain ⟨full, hfullBound, hfullRep⟩ := full_physical_monitor_weights C0 Fm
  refine ⟨loc, full,
    represent_all_core_monitors H F outer bad Mon loc hlocRep,
    hfullRep, ?_, ?_⟩
  · intro j T hT
    have hbound := hlocTri j T hT
    have hLloc : S07V39.glueConst β (B * D) ≤ L := by
      dsimp [L]
      linarith [le_max_left (S07V39.glueConst β (B * D)) D]
    have hnon : (0 : ℝ) ≤ 3 * (T∩bad).card := by positivity
    have hm := mul_le_mul_of_nonneg_right hLloc hnon
    dsimp [D] at hbound hLloc
    calc
      |triSum (loc j) T| ≤
          3 * S07V39.glueConst β (B * (M * (d * c) : ℕ)) * (T∩bad).card := hbound
      _ = S07V39.glueConst β (B * (M * (d * c) : ℕ)) *
          (3 * (T∩bad).card) := by ring
      _ ≤ L * (3 * (T∩bad).card) := hm
      _ = 3 * L * (T∩bad).card := by ring
  · intro j T hT
    have hbase := triangle_moment_bound hT D (Nat.cast_nonneg _) (full j)
      (hfullBound j)
    have hDle : D ≤ L := by
      dsimp [L]
      linarith [le_max_right (S07V39.glueConst β (B * D)) D]
    have hcard : T.card = 3 := hT.1
    have hDnon : 0 ≤ D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hDle
      (show (0 : ℝ) ≤ 3 * (T.card : ℝ) by positivity)
    calc
      |triSum (full j) T| ≤ 3 * D := hbase
      _ ≤ D * (3 * (T.card : ℝ)) := by rw [hcard]; norm_num; nlinarith [hDnon]
      _ ≤ L * (3 * (T.card : ℝ)) := hmul
      _ = 3 * L * (T.card : ℝ) := by ring

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.uniform_physical_monitor_weights
