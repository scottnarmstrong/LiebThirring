/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Explicit normalized interval modes

The one-dimensional factors of the cube spectral theory, on an interval of length
`ℓ > 0`. These lemmas verify normalization, classical boundary conditions
and the `π² n² / ℓ²` kinetic coefficient. They do not assert completeness
or the quadratic-form identity for arbitrary Sobolev functions.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace LiebThirring.TFCubes

noncomputable def intervalFrequency (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) : ℝ :=
  Real.pi * n / ℓ.val

noncomputable def dirichletIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt (2 / ℓ.val) * Real.sin (intervalFrequency ℓ n * x)

noncomputable def neumannIntervalCoefficient (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) : ℝ :=
  if n = 0 then (Real.sqrt ℓ.val)⁻¹ else Real.sqrt (2 / ℓ.val)

noncomputable def neumannIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) : ℝ :=
  neumannIntervalCoefficient ℓ n * Real.cos (intervalFrequency ℓ n * x)

theorem intervalFrequency_mul_length (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    intervalFrequency ℓ n * ℓ.val = n * Real.pi := by
  unfold intervalFrequency
  rw [div_mul_cancel₀ _ ℓ.property.ne']
  ring

theorem intervalFrequency_pos (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : 0 < n) :
    0 < intervalFrequency ℓ n :=
  div_pos (mul_pos Real.pi_pos (Nat.cast_pos.mpr hn)) ℓ.property

theorem intervalFrequency_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    intervalFrequency ℓ n ^ 2 = Real.pi ^ 2 * (n : ℝ) ^ 2 / ℓ.val ^ 2 := by
  simp only [intervalFrequency, div_pow, mul_pow]

theorem hasDerivAt_dirichletIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) :
    HasDerivAt (dirichletIntervalMode ℓ n)
      (Real.sqrt (2 / ℓ.val) * Real.cos (intervalFrequency ℓ n * x) * intervalFrequency ℓ n) x := by
  unfold dirichletIntervalMode
  simpa only [dirichletIntervalMode, id_eq, mul_one, mul_assoc] using
    (((hasDerivAt_id x).const_mul (intervalFrequency ℓ n)).sin).const_mul
      (Real.sqrt (2 / ℓ.val))

theorem deriv_dirichletIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) :
    deriv (dirichletIntervalMode ℓ n) x =
      Real.sqrt (2 / ℓ.val) * Real.cos (intervalFrequency ℓ n * x) * intervalFrequency ℓ n :=
  (hasDerivAt_dirichletIntervalMode ℓ n x).deriv

theorem neumannIntervalMode_zero (ℓ : {ℓ : ℝ // 0 < ℓ}) (x : ℝ) :
    neumannIntervalMode ℓ 0 x = (Real.sqrt ℓ.val)⁻¹ := by
  simp [neumannIntervalMode, neumannIntervalCoefficient, intervalFrequency]

theorem integral_sin_frequency_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : 0 < n) :
    (∫ x in 0..ℓ.val, Real.sin (intervalFrequency ℓ n * x) ^ 2) = ℓ.val / 2 := by
  rw [integral_comp_mul_left (fun x => Real.sin x ^ 2) (intervalFrequency_pos ℓ hn).ne',
    integral_sin_sq]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul,
    intervalFrequency_mul_length, Real.sin_nat_mul_pi, sub_zero,
    smul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  unfold intervalFrequency
  field_simp
  ring

theorem integral_cos_frequency_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : 0 < n) :
    (∫ x in 0..ℓ.val, Real.cos (intervalFrequency ℓ n * x) ^ 2) = ℓ.val / 2 := by
  rw [integral_comp_mul_left (fun x => Real.cos x ^ 2) (intervalFrequency_pos ℓ hn).ne',
    integral_cos_sq]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero,
    intervalFrequency_mul_length, Real.sin_nat_mul_pi, mul_zero, sub_zero,
    zero_add, smul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  unfold intervalFrequency
  field_simp

theorem integral_dirichletIntervalMode_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    (∫ x in 0..ℓ.val, dirichletIntervalMode ℓ n x ^ 2) = 1 := by
  simp only [dirichletIntervalMode, mul_pow]
  rw [intervalIntegral.integral_const_mul, Real.sq_sqrt (div_nonneg (by norm_num) ℓ.property.le)]
  erw [integral_sin_frequency_sq ℓ n.property]
  field_simp [ℓ.property.ne']

theorem integral_neumannIntervalMode_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    (∫ x in 0..ℓ.val, neumannIntervalMode ℓ n x ^ 2) = 1 := by
  by_cases hn : n = 0
  · subst n
    simp only [neumannIntervalMode_zero, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, inv_pow]
    rw [Real.sq_sqrt ℓ.property.le]
    exact mul_inv_cancel₀ ℓ.property.ne'
  · simp only [neumannIntervalMode, mul_pow, neumannIntervalCoefficient, ite_eq_right hn]
    rw [intervalIntegral.integral_const_mul, Real.sq_sqrt (div_nonneg (by norm_num) ℓ.property.le),
      integral_cos_frequency_sq ℓ (Nat.pos_of_ne_zero hn)]
    field_simp [ℓ.property.ne']

end LiebThirring.TFCubes

end
