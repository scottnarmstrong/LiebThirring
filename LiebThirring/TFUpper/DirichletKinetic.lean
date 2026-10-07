/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletKineticGraph

/-!
# Exact kinetic energy of a zero-extended Dirichlet cube orbital

The closed weak-gradient construction and the product derivative norms give
the literal Dirichlet eigenvalue, with the Fourier normalization.
explicit sine-product construction.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open LiebThirring.Sobolev

namespace LiebThirring.TFUpper

noncomputable def dirichletCubeOrbitalDerivativeState {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 1 × Fin 3) : State 1 q :=
  spatialSpinToState q (dirichletCubeDerivativeSpatialL2 ℓ b p a.2)

theorem hasWeakDerivative_dirichletCubeOrbitalDerivativeState {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 1 × Fin 3) :
    HasWeakDerivative a (dirichletCubeOrbital ℓ b p)
      (dirichletCubeOrbitalDerivativeState ℓ b p a) := by
  obtain ⟨i, c⟩ := a
  simpa only [dirichletCubeOrbitalDerivativeState,
    Subsingleton.elim i 0] using hasWeakDerivative_dirichletCubeOrbital ℓ b p c

theorem sum_norm_dirichletCubeOrbitalDerivativeState_sq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    (∑ a : Fin 1 × Fin 3, ‖dirichletCubeOrbitalDerivativeState ℓ b p a‖ ^ 2) =
      TFCubes.dirichletCubeEigenvalue ℓ p := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  change (∑ a : Fin 3,
    ‖spatialSpinToState q (dirichletCubeDerivativeSpatialL2 ℓ b p a)‖ ^ 2) = _
  simp_rw [(spatialSpinToState q).norm_map]
  change (∑ a : Fin 3,
    ‖TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
      ((memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
        (dirichletCubeDerivativeValue ℓ b p a))‖ ^ 2) = _
  simp_rw [TFCubes.norm_regionZeroExtendL2]
  exact sum_norm_toLp_dirichletCubeDerivativeValue_sq ℓ b p

theorem kineticEnergy_dirichletCubeOrbital_toReal {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    (kineticEnergy (dirichletCubeOrbital ℓ b p)).toReal =
      TFCubes.dirichletCubeEigenvalue ℓ p := by
  rw [kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq
    (dirichletCubeOrbital ℓ b p) (dirichletCubeOrbitalDerivativeState ℓ b p)
    (hasWeakDerivative_dirichletCubeOrbitalDerivativeState ℓ b p)]
  exact sum_norm_dirichletCubeOrbitalDerivativeState_sq ℓ b p

theorem kineticEnergy_dirichletCubeOrbital_lt_top {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    kineticEnergy (dirichletCubeOrbital ℓ b p) < ⊤ := by
  rw [kineticEnergy_eq_sum_weakDerivative_nnnorm_sq
    (dirichletCubeOrbital ℓ b p) (dirichletCubeOrbitalDerivativeState ℓ b p)
    (hasWeakDerivative_dirichletCubeOrbitalDerivativeState ℓ b p)]
  exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.pow_lt_top ENNReal.coe_lt_top

end LiebThirring.TFUpper

end
