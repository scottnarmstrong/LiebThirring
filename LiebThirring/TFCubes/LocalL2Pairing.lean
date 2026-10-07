/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.RegionL2
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Supported pairings and physical L² restriction

Restriction preserves the pairing with any test function supported in the
region. The result is an identity of literal integrals and imposes no
boundary regularity on the restricted state.
-/

public section

open MeasureTheory

namespace LiebThirring.TFCubes

variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A supported test has the same pairing with a global state and its restriction. -/
theorem integral_inner_regionRestrictL2 (μ : Measure E) (Ω : Set E)
    (η : E → F) (hη : tsupport η ⊆ Ω) (u : Lp F 2 μ) :
    (∫ x in Ω, inner ℂ (η x) (regionRestrictL2 μ Ω u x) ∂μ) =
      ∫ x, inner ℂ (η x) (u x) ∂μ := by
  calc
    _ = ∫ x in Ω, inner ℂ (η x) (u x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [regionRestrictL2_ae μ Ω u] with x hx
      rw [hx]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hx' : x ∉ tsupport η := fun h ↦ hx (hη h)
      rw [image_eq_zero_of_notMem_tsupport hx', inner_zero_left])

end LiebThirring.TFCubes

end
