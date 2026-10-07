/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalL2Pairing
public import LiebThirring.TFCubes.LocalWeakDerivative
public import LiebThirring.Sobolev.WeakDerivative

/-!
# Restriction of physical weak derivatives

Global weak derivatives restrict to the literal local distributional
identity. Tests and their derivatives vanish off the region, so no global
derivative of an indicator is introduced. This is the restriction input to
the local Neumann forms of the cube spectral theory and Neumann sector estimate.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace LiebThirring.Sobolev

/-- Restrict a global coordinate weak derivative to a region, testing only
against compact smooth functions supported inside that region. -/
theorem HasWeakDerivative.restrict_region {N q : ℕ} {a : Fin N × Fin 3}
    {u g : State N q} (h : HasWeakDerivative a u g) (Ω : Set (Configuration N)) :
    TFCubes.HasWeakDerivativeOn Ω (coordinateVector a)
      (TFCubes.regionRestrictL2 volume Ω u) (TFCubes.regionRestrictL2 volume Ω g) := by
  intro η hηc hηs hηΩ
  rw [TFCubes.integral_inner_regionRestrictL2 volume Ω η hηΩ g,
    TFCubes.integral_inner_regionRestrictL2 volume Ω
      (fun x ↦ fderiv ℝ η x (coordinateVector a))
      ((tsupport_fderiv_apply_subset ℝ (coordinateVector a)).trans hηΩ) u]
  exact h η hηc hηs

end LiebThirring.Sobolev

end
