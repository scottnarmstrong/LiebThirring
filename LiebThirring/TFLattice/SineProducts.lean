/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.OneDimensionalModes
import Mathlib.Tactic

/-!
# Sine-square products for filled Dirichlet densities

The extra factor `3/2` occurs precisely when the two positive frequencies
coincide. These are density products, not the mode orthogonality or form
identities assigned to cube spectral theory. Source: Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace LiebThirring.TFLattice

open TFCubes

theorem integral_cos_integer_frequency (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℤ) :
    (∫ x in 0..ℓ.val, Real.cos (Real.pi * n / ℓ.val * x)) =
      if n = 0 then ℓ.val else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hc : Real.pi * (n : ℝ) / ℓ.val ≠ 0 := by
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr hn)) ℓ.property.ne'
    have he : Real.pi * (n : ℝ) / ℓ.val * ℓ.val = (n : ℝ) * Real.pi := by
      rw [div_mul_cancel₀ _ ℓ.property.ne']
      ring
    rw [integral_comp_mul_left _ hc, integral_cos]
    simp [he, Real.sin_int_mul_pi, hn]

theorem sin_sq_mul_sin_sq (a b : ℝ) :
    Real.sin a ^ 2 * Real.sin b ^ 2 =
      (1 : ℝ) / 4 - Real.cos (2 * a) / 4 - Real.cos (2 * b) / 4 +
        Real.cos (2 * (a - b)) / 8 + Real.cos (2 * (a + b)) / 8 := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have hc := Real.two_mul_cos_mul_cos (2 * a) (2 * b)
  rw [← mul_sub, ← mul_add] at hc
  nlinarith

/-- Unnormalized sine-square overlap, including the repeated-frequency case. -/
theorem integral_sin_frequency_sq_mul_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) (n m : ℕ+) :
    (∫ x in 0..ℓ.val,
      Real.sin (intervalFrequency ℓ n * x) ^ 2 *
        Real.sin (intervalFrequency ℓ m * x) ^ 2) =
      if n = m then 3 * ℓ.val / 8 else ℓ.val / 4 := by
  have hfreq (j : ℕ+) (x : ℝ) :
      2 * (intervalFrequency ℓ j * x) =
        Real.pi * ((2 * (j : ℤ) : ℤ) : ℝ) / ℓ.val * x := by
    simp only [intervalFrequency, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  have hsub (x : ℝ) :
      2 * (intervalFrequency ℓ n * x - intervalFrequency ℓ m * x) =
        Real.pi * ((2 * ((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) / ℓ.val * x := by
    simp only [intervalFrequency, Int.cast_mul, Int.cast_ofNat, Int.cast_sub,
      Int.cast_natCast]
    ring
  have hadd (x : ℝ) :
      2 * (intervalFrequency ℓ n * x + intervalFrequency ℓ m * x) =
        Real.pi * ((2 * ((n : ℤ) + (m : ℤ)) : ℤ) : ℝ) / ℓ.val * x := by
    simp only [intervalFrequency, Int.cast_mul, Int.cast_ofNat, Int.cast_add,
      Int.cast_natCast]
    ring
  simp_rw [sin_sq_mul_sin_sq, hfreq, hsub, hadd]
  have hint (j : ℤ) : IntervalIntegrable
      (fun x => Real.cos (Real.pi * j / ℓ.val * x) / 8) volume 0 ℓ.val :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hint4 (j : ℤ) : IntervalIntegrable
      (fun x => Real.cos (Real.pi * j / ℓ.val * x) / 4) volume 0 ℓ.val :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [integral_add ((intervalIntegrable_const.sub (hint4 _)).sub (hint4 _)
      |>.add (hint _)) (hint _),
    integral_add ((intervalIntegrable_const.sub (hint4 _)).sub (hint4 _)) (hint _),
    integral_sub (intervalIntegrable_const.sub (hint4 _)) (hint4 _),
    integral_sub intervalIntegrable_const (hint4 _)]
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    integral_cos_integer_frequency]
  have hnpos : (0 : ℤ) < n := by exact_mod_cast n.property
  have hmpos : (0 : ℤ) < m := by exact_mod_cast m.property
  have hn : (2 * (n : ℤ)) ≠ 0 := by omega
  have hm : (2 * (m : ℤ)) ≠ 0 := by omega
  have hnm : 2 * ((n : ℤ) + (m : ℤ)) ≠ 0 := by
    omega
  have heq : 2 * ((n : ℤ) - (m : ℤ)) = 0 ↔ n = m := by
    constructor
    · intro h
      apply PNat.eq
      omega
    · intro h
      simp [h]
  simp only [ite_eq_right hn, ite_eq_right hm, ite_eq_right hnm, heq]
  split_ifs <;> ring

/-- Normalized factors have overlap `1/ℓ` off the diagonal, and `3/(2ℓ)`
on the diagonal. Spin labels are absent because these are spatial densities. -/
theorem integral_dirichletIntervalMode_sq_mul_sq
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n m : ℕ+) :
    (∫ x in 0..ℓ.val, dirichletIntervalMode ℓ n x ^ 2 *
      dirichletIntervalMode ℓ m x ^ 2) =
      if n = m then 3 / (2 * ℓ.val) else 1 / ℓ.val := by
  simp only [dirichletIntervalMode, mul_pow,
    Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ℓ.property.le)]
  have heq (x : ℝ) :
      (2 / ℓ.val * Real.sin (intervalFrequency ℓ n * x) ^ 2) *
        (2 / ℓ.val * Real.sin (intervalFrequency ℓ m * x) ^ 2) =
      (2 / ℓ.val) ^ 2 * (Real.sin (intervalFrequency ℓ n * x) ^ 2 *
        Real.sin (intervalFrequency ℓ m * x) ^ 2) := by ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, integral_sin_frequency_sq_mul_sq]
  split_ifs <;> field_simp [ℓ.property.ne'] <;> ring

end LiebThirring.TFLattice

end
