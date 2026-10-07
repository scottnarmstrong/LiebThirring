/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalModesL2
public import LiebThirring.TFCubes.RegionL2
public import LiebThirring.TFCubes.LocalWeakDerivative
public import LiebThirring.TFLattice.Indices
public import LiebThirring.Defs.Configuration
import Mathlib.Tactic

/-! # Literal modes on translated three-dimensional cubes

The spatial factors are the normalized interval sine and cosine modes, evaluated
at the translated coordinates `x i - b i`.  Spin is represented in the genuine
Euclidean Hilbert space, with one standard basis vector attached to each spatial
mode.  Form identities and completeness are developed in subsequent modules.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace LiebThirring.TFCubes

/-- The open cube `b + (0,ℓ)^3`. -/
def cubeInterior (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) : Set Position :=
  {x | ∀ i, b i < x i ∧ x i < b i + ℓ.val}

theorem isOpen_cubeInterior (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    IsOpen (cubeInterior b ℓ) := by
  rw [show cubeInterior b ℓ = ⋂ i : Fin 3,
      {x : Position | b i < x i ∧ x i < b i + ℓ.val} by
    ext x
    simp only [cubeInterior, mem_iInter, mem_ofPred_eq]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (by fun_prop : Continuous (fun x : Position => x i))

theorem measurableSet_cubeInterior (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    MeasurableSet (cubeInterior b ℓ) := (isOpen_cubeInterior b ℓ).measurableSet

/-- Positive spatial frequencies and a spin label. -/
abbrev DirichletCubeModeIndex (q : ℕ) := (Fin 3 → ℕ+) × Fin q

/-- The one-particle spin Hilbert space, indexed directly by the `q` spin labels. -/
abbrev CubeSpin (q : ℕ) := EuclideanSpace ℂ (Fin q)

/-- Local one-particle spin states on a translated cube. -/
noncomputable abbrev CubeState (q : ℕ) (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) :=
  RegionState Position (CubeSpin q) (cubeInterior b ℓ)

/-- The literal normalized Dirichlet spatial product. -/
noncomputable def dirichletCubeSpatialMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ+) (x : Position) : ℂ :=
  ∏ i : Fin 3, (dirichletIntervalMode ℓ (k i) (x i - b i) : ℂ)

/-- The literal normalized Neumann spatial product, including zero coordinates. -/
noncomputable def neumannCubeSpatialMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ) (x : Position) : ℂ :=
  ∏ i : Fin 3, (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ)

/-- Dirichlet cube mode with its standard spin vector. -/
noncomputable def dirichletCubeModeValue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) (x : Position) : CubeSpin q :=
  EuclideanSpace.single p.2 (dirichletCubeSpatialMode ℓ b p.1 x)

/-- Neumann cube mode with its standard spin vector. -/
noncomputable def neumannCubeModeValue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : TFLattice.ModeIndex q) (x : Position) : CubeSpin q :=
  EuclideanSpace.single p.2 (neumannCubeSpatialMode ℓ b p.1 x)

theorem dirichletCubeModeValue_apply {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) (x : Position) (s : Fin q) :
    dirichletCubeModeValue ℓ b p x s =
      if s = p.2 then dirichletCubeSpatialMode ℓ b p.1 x else 0 := by
  simp [dirichletCubeModeValue]

theorem neumannCubeModeValue_apply {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : TFLattice.ModeIndex q) (x : Position) (s : Fin q) :
    neumannCubeModeValue ℓ b p x s =
      if s = p.2 then neumannCubeSpatialMode ℓ b p.1 x else 0 := by
  simp [neumannCubeModeValue]

/-- Squared Dirichlet frequency, written as a sum of its interval factors. -/
noncomputable def dirichletCubeEigenvalue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (p : DirichletCubeModeIndex q) : ℝ :=
  ∑ i : Fin 3, intervalFrequency ℓ (p.1 i) ^ 2

theorem neumannCubeEigenvalue_eq_sum_intervalFrequency_sq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (p : TFLattice.ModeIndex q) :
    TFLattice.cubeEigenvalue ℓ p = ∑ i : Fin 3, intervalFrequency ℓ (p.1 i) ^ 2 := by
  simp only [intervalFrequency_sq, TFLattice.cubeEigenvalue, TFLattice.squaredRadius]
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem dirichletCubeEigenvalue_eq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (p : DirichletCubeModeIndex q) :
    dirichletCubeEigenvalue ℓ p =
      Real.pi ^ 2 * (TFLattice.squaredRadius (fun i => (p.1 i : ℕ)) : ℝ) / ℓ.val ^ 2 := by
  simp only [dirichletCubeEigenvalue, intervalFrequency_sq, TFLattice.squaredRadius]
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

end LiebThirring.TFCubes

end
