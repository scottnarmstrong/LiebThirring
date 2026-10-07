/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes
public import LiebThirring.TFSectors.SectorSpectralSums

/-! # Scalar spatial eigenvalues in the sector normalization -/

@[expose] public section
namespace LiebThirring.TFProduct

/-- The cube eigenvalue depends only on its three spatial frequencies. -/
noncomputable def scalarCubeEigenvalue (ℓ : {x : ℝ // 0 < x}) (k : Fin 3 → ℕ) : ℝ :=
  TFLattice.cubeEigenvalue ℓ (k, (0 : Fin 1))

theorem scalarCubeEigenvalue_nonneg (ℓ : {x : ℝ // 0 < x}) (k : Fin 3 → ℕ) :
    0 ≤ scalarCubeEigenvalue ℓ k := TFLattice.cubeEigenvalue_nonneg _ _

theorem scalarCubeEigenvalue_eq_sum (ℓ : {x : ℝ // 0 < x}) (k : Fin 3 → ℕ) :
    scalarCubeEigenvalue ℓ k = ∑ a : Fin 3, TFCubes.intervalFrequency ℓ (k a) ^ 2 :=
  TFCubes.neumannCubeEigenvalue_eq_sum_intervalFrequency_sq ℓ _

theorem productEigenvalue_eq_sum_scalar {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (k : Fin N → TFLattice.ModeIndex q) :
    TFSectors.productEigenvalue ℓ k = ∑ i : Fin N, scalarCubeEigenvalue ℓ (k i).1 := rfl

end LiebThirring.TFProduct
end
