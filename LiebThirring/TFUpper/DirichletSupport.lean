/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletOrbitals

/-! # Support separation for spatial Dirichlet cube orbitals -/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace LiebThirring.TFUpper

/-- Spatial orbitals supported in disjoint cube interiors are orthogonal. -/
theorem inner_dirichletCubeSpatialL2_eq_zero_of_disjoint {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b c : Position)
    (p r : TFCubes.DirichletCubeModeIndex q)
    (hdis : Disjoint (TFCubes.cubeInterior b ℓ) (TFCubes.cubeInterior c ℓ)) :
    inner ℂ (dirichletCubeSpatialL2 ℓ b p)
      (dirichletCubeSpatialL2 ℓ c r) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [dirichletCubeSpatialL2_ae ℓ b p,
    dirichletCubeSpatialL2_ae ℓ c r] with x hp hr
  rw [hp, hr]
  by_cases hb : x ∈ TFCubes.cubeInterior b ℓ
  · have hc : x ∉ TFCubes.cubeInterior c ℓ := fun hc => Set.disjoint_left.mp hdis hb hc
    rw [indicator_of_mem hb, indicator_of_notMem hc, inner_zero_right]
    simp
  · rw [indicator_of_notMem hb, inner_zero_left]
    simp

end LiebThirring.TFUpper

end
