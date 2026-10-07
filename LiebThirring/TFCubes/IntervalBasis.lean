/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalCoefficients

/-!
# Complete physical interval sine and cosine bases

One-dimensional L² completeness. Literal odd/even reflection,
the coefficient equations, and circle Fourier uniqueness prove totality of the
physical sine/cosine families. Together with their orthonormality this yields
actual `HilbertBasis`es on the restricted physical Lebesgue L² carrier.
-/

@[expose] public section

open MeasureTheory Set Submodule AddCircle
open scoped InnerProductSpace ENNReal

namespace LiebThirring.TFCubes

/-- Positive sine coefficients determine an interval L² function. -/
theorem eq_zero_of_dirichletIntervalModeL2_inner_eq_zero
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val)))
    (hu : ∀ n : ℕ+, ⟪dirichletIntervalModeL2 ℓ n, u⟫_ℂ = 0) : u = 0 := by
  have hz : intervalReflectionL2 ℓ true u = 0 :=
    eq_zero_of_odd_positive_fourierCoeff_eq_zero _ (intervalReflectionL2_odd ℓ u) (fun n ↦ by
      rw [fourierCoeff_intervalReflectionL2_odd_pos, hu n, mul_zero])
  apply (intervalReflectionLI ℓ true).injective
  rw [intervalReflectionLI_apply, map_zero]
  exact hz

/-- Cosine coefficients, including the constant coefficient, determine interval L². -/
theorem eq_zero_of_neumannIntervalModeL2_inner_eq_zero
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val)))
    (hu : ∀ n : ℕ, ⟪neumannIntervalModeL2 ℓ n, u⟫_ℂ = 0) : u = 0 := by
  have hz : intervalReflectionL2 ℓ false u = 0 :=
    eq_zero_of_even_positive_fourierCoeff_eq_zero _ (intervalReflectionL2_even ℓ u)
      (by rw [fourierCoeff_intervalReflectionL2_even_zero, hu 0])
      (fun n ↦ by rw [fourierCoeff_intervalReflectionL2_even_pos, hu n, zero_div])
  apply (intervalReflectionLI ℓ false).injective
  rw [intervalReflectionLI_apply, map_zero]
  exact hz

theorem dirichletIntervalModeL2_span_orthogonal_eq_bot (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    (span ℂ (range (dirichletIntervalModeL2 ℓ)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [mem_bot]
  apply eq_zero_of_dirichletIntervalModeL2_inner_eq_zero ℓ u
  intro n
  exact inner_right_of_mem_orthogonal (subset_span (mem_range_self n)) hu

theorem neumannIntervalModeL2_span_orthogonal_eq_bot (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    (span ℂ (range (neumannIntervalModeL2 ℓ)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [mem_bot]
  apply eq_zero_of_neumannIntervalModeL2_inner_eq_zero ℓ u
  intro n
  exact inner_right_of_mem_orthogonal (subset_span (mem_range_self n)) hu

/-- The complete positive sine basis of physical interval L². -/
noncomputable def dirichletIntervalBasis (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    HilbertBasis ℕ+ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_dirichletIntervalModeL2 ℓ)
    (dirichletIntervalModeL2_span_orthogonal_eq_bot ℓ)

/-- The complete cosine basis of physical interval L², with one constant mode. -/
noncomputable def neumannIntervalBasis (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_neumannIntervalModeL2 ℓ)
    (neumannIntervalModeL2_span_orthogonal_eq_bot ℓ)

@[simp] theorem dirichletIntervalBasis_apply (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    dirichletIntervalBasis ℓ n = dirichletIntervalModeL2 ℓ n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

@[simp] theorem neumannIntervalBasis_apply (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    neumannIntervalBasis ℓ n = neumannIntervalModeL2 ℓ n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

end LiebThirring.TFCubes

end
