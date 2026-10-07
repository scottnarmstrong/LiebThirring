/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModesL2

/-! # Spatial Dirichlet cube orbitals

This module supplies the literal normalized spatial-spin orbitals used in the
Dirichlet-cube trial for the cube spectral theory. It uses only the
finite-mode part of the cube API; no completeness or form identity is asserted.
-/

public section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace LiebThirring.TFUpper

/-- The local normalized sine-product mode, extended by zero to physical space. -/
@[expose] noncomputable def dirichletCubeSpatialL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) :=
  TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
    (TFCubes.dirichletCubeModeL2 ℓ b p)

/-- The extended orbital is represented by the literal sine product inside
the open cube and by zero outside it. -/
theorem dirichletCubeSpatialL2_ae {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    dirichletCubeSpatialL2 ℓ b p =ᵐ[volume]
      (TFCubes.cubeInterior b ℓ).indicator
        (TFCubes.dirichletCubeModeValue ℓ b p) := by
  have hz := TFCubes.regionZeroExtendL2_ae volume
    (TFCubes.measurableSet_cubeInterior b ℓ)
    (TFCubes.dirichletCubeModeL2 ℓ b p)
  have hl := TFCubes.dirichletCubeModeL2_ae ℓ b p
  have hl' : ∀ᵐ x : Position ∂volume, x ∈ TFCubes.cubeInterior b ℓ →
      TFCubes.dirichletCubeModeL2 ℓ b p x =
        TFCubes.dirichletCubeModeValue ℓ b p x :=
    (ae_restrict_iff' (TFCubes.measurableSet_cubeInterior b ℓ)).mp hl
  have hi : (TFCubes.cubeInterior b ℓ).indicator
      (TFCubes.dirichletCubeModeL2 ℓ b p) =ᵐ[volume]
      (TFCubes.cubeInterior b ℓ).indicator
        (TFCubes.dirichletCubeModeValue ℓ b p) := by
    filter_upwards [hl'] with x hx
    by_cases hmem : x ∈ TFCubes.cubeInterior b ℓ
    · simp only [indicator_of_mem hmem, hx hmem]
    · simp only [indicator_of_notMem hmem]
  exact hz.trans hi

end LiebThirring.TFUpper

end
