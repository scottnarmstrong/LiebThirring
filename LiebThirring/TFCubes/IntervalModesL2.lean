/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.OneDimensionalModes
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Physical interval modes in complex L²

The literal sine and cosine modes from `OneDimensionalModes`, viewed in
`Lp ℂ 2 (volume.restrict (Set.Ioo 0 ℓ.val))`. This is a leaf of the cube spectral theory:
normalization and orthogonality do not assert completeness or any form identity.
-/

@[expose] public section

open MeasureTheory intervalIntegral
open scoped InnerProductSpace

namespace LiebThirring.TFCubes

/-- A continuous real function on the finite physical interval belongs to complex L². -/
theorem memLp_ofReal_interval {f : ℝ → ℝ} (hf : Continuous f)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    MemLp (fun x => (f x : ℂ)) 2 (volume.restrict (Set.Ioo 0 ℓ.val)) := by
  have hc : Continuous (fun x => (f x : ℂ)) := Complex.continuous_ofReal.comp hf
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (hc.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

theorem continuous_dirichletIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    Continuous (dirichletIntervalMode ℓ n) := by
  unfold dirichletIntervalMode
  fun_prop

theorem continuous_neumannIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    Continuous (neumannIntervalMode ℓ n) := by
  unfold neumannIntervalMode
  fun_prop

theorem dirichletIntervalMode_memLp (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    MemLp (fun x => (dirichletIntervalMode ℓ n x : ℂ)) 2
      (volume.restrict (Set.Ioo 0 ℓ.val)) :=
  memLp_ofReal_interval (continuous_dirichletIntervalMode ℓ n) ℓ

theorem neumannIntervalMode_memLp (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    MemLp (fun x => (neumannIntervalMode ℓ n x : ℂ)) 2
      (volume.restrict (Set.Ioo 0 ℓ.val)) :=
  memLp_ofReal_interval (continuous_neumannIntervalMode ℓ n) ℓ

/-- The normalized physical Dirichlet mode, represented by its literal sine formula. -/
noncomputable def dirichletIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    Lp ℂ 2 (volume.restrict (Set.Ioo 0 ℓ.val)) :=
  (dirichletIntervalMode_memLp ℓ n).toLp (fun x => (dirichletIntervalMode ℓ n x : ℂ))

/-- The normalized physical Neumann mode, including its constant zero mode. -/
noncomputable def neumannIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    Lp ℂ 2 (volume.restrict (Set.Ioo 0 ℓ.val)) :=
  (neumannIntervalMode_memLp ℓ n).toLp (fun x => (neumannIntervalMode ℓ n x : ℂ))

theorem dirichletIntervalModeL2_ae (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    dirichletIntervalModeL2 ℓ n =ᵐ[volume.restrict (Set.Ioo 0 ℓ.val)]
      (fun x => (dirichletIntervalMode ℓ n x : ℂ)) :=
  (dirichletIntervalMode_memLp ℓ n).coeFn_toLp

theorem neumannIntervalModeL2_ae (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    neumannIntervalModeL2 ℓ n =ᵐ[volume.restrict (Set.Ioo 0 ℓ.val)]
      (fun x => (neumannIntervalMode ℓ n x : ℂ)) :=
  (neumannIntervalMode_memLp ℓ n).coeFn_toLp

theorem inner_dirichletIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (m n : ℕ+) :
    ⟪dirichletIntervalModeL2 ℓ m, dirichletIntervalModeL2 ℓ n⟫_ℂ =
      (↑(∫ x in 0..ℓ.val, (dirichletIntervalMode ℓ m x * dirichletIntervalMode ℓ n x : ℝ)) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Set.Ioo 0 ℓ.val,
        (↑(dirichletIntervalMode ℓ m x * dirichletIntervalMode ℓ n x : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [dirichletIntervalModeL2_ae ℓ m, dirichletIntervalModeL2_ae ℓ n]
        with x hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
    _ = _ := by
      rw [integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ℓ.property.le]

theorem inner_neumannIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (m n : ℕ) :
    ⟪neumannIntervalModeL2 ℓ m, neumannIntervalModeL2 ℓ n⟫_ℂ =
      (↑(∫ x in 0..ℓ.val, (neumannIntervalMode ℓ m x * neumannIntervalMode ℓ n x : ℝ)) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Set.Ioo 0 ℓ.val,
        (↑(neumannIntervalMode ℓ m x * neumannIntervalMode ℓ n x : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [neumannIntervalModeL2_ae ℓ m, neumannIntervalModeL2_ae ℓ n]
        with x hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
    _ = _ := by
      rw [integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ℓ.property.le]

theorem inner_dirichletIntervalModeL2_self (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    ⟪dirichletIntervalModeL2 ℓ n, dirichletIntervalModeL2 ℓ n⟫_ℂ = 1 := by
  rw [inner_dirichletIntervalModeL2]
  simp only [← pow_two, integral_dirichletIntervalMode_sq, Complex.ofReal_one]

theorem inner_neumannIntervalModeL2_self (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    ⟪neumannIntervalModeL2 ℓ n, neumannIntervalModeL2 ℓ n⟫_ℂ = 1 := by
  rw [inner_neumannIntervalModeL2]
  simp only [← pow_two, integral_neumannIntervalMode_sq, Complex.ofReal_one]

theorem norm_dirichletIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    ‖dirichletIntervalModeL2 ℓ n‖ = 1 := by
  have h : ‖dirichletIntervalModeL2 ℓ n‖ ^ 2 = 1 ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_dirichletIntervalModeL2_self]
    simp only [RCLike.one_re, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

theorem norm_neumannIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    ‖neumannIntervalModeL2 ℓ n‖ = 1 := by
  have h : ‖neumannIntervalModeL2 ℓ n‖ ^ 2 = 1 ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_neumannIntervalModeL2_self]
    simp only [RCLike.one_re, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

theorem intervalFrequency_injective (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Function.Injective (intervalFrequency ℓ) := by
  intro m n h
  have heq := congrArg (fun r : ℝ => r * ℓ.val) h
  rw [intervalFrequency_mul_length, intervalFrequency_mul_length] at heq
  have hcast : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ Real.pi_ne_zero heq
  exact Nat.cast_injective hcast

theorem intervalFrequency_nonneg (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    0 ≤ intervalFrequency ℓ n :=
  div_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)) ℓ.property.le

/-- Integrating a nonzero cosine frequency whose sine vanishes at the far endpoint. -/
theorem integral_cos_mul_of_sin_eq_zero (ℓ : {ℓ : ℝ // 0 < ℓ})
    {a : ℝ} (ha : a ≠ 0) (hend : Real.sin (a * ℓ.val) = 0) :
    (∫ x in 0..ℓ.val, Real.cos (a * x)) = 0 := by
  rw [integral_comp_mul_left Real.cos ha, integral_cos]
  simp only [mul_zero, hend, Real.sin_zero, sub_self, smul_zero]

theorem integral_cos_frequency_sub (ℓ : {ℓ : ℝ // 0 < ℓ}) {m n : ℕ}
    (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, Real.cos ((intervalFrequency ℓ m - intervalFrequency ℓ n) * x)) = 0 := by
  apply integral_cos_mul_of_sin_eq_zero ℓ
  · exact sub_ne_zero.mpr ((intervalFrequency_injective ℓ).ne hmn)
  · rw [sub_mul, intervalFrequency_mul_length, intervalFrequency_mul_length, Real.sin_sub]
    simp only [Real.sin_nat_mul_pi, zero_mul, mul_zero, sub_zero]

theorem integral_cos_frequency_add (ℓ : {ℓ : ℝ // 0 < ℓ}) {m n : ℕ}
    (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, Real.cos ((intervalFrequency ℓ m + intervalFrequency ℓ n) * x)) = 0 := by
  apply integral_cos_mul_of_sin_eq_zero ℓ
  · intro hz
    have hm : intervalFrequency ℓ m = 0 :=
      (add_eq_zero_iff_of_nonneg (intervalFrequency_nonneg ℓ m)
        (intervalFrequency_nonneg ℓ n)).mp hz |>.1
    have hn : intervalFrequency ℓ n = 0 :=
      (add_eq_zero_iff_of_nonneg (intervalFrequency_nonneg ℓ m)
        (intervalFrequency_nonneg ℓ n)).mp hz |>.2
    exact hmn ((intervalFrequency_injective ℓ) (hm.trans hn.symm))
  · rw [add_mul, intervalFrequency_mul_length, intervalFrequency_mul_length, Real.sin_add]
    simp only [Real.sin_nat_mul_pi, zero_mul, mul_zero, add_zero]

theorem integral_sin_frequency_mul_sin_frequency (ℓ : {ℓ : ℝ // 0 < ℓ}) {m n : ℕ}
    (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, Real.sin (intervalFrequency ℓ m * x) *
      Real.sin (intervalFrequency ℓ n * x)) = 0 := by
  have heq (x : ℝ) : Real.sin (intervalFrequency ℓ m * x) *
      Real.sin (intervalFrequency ℓ n * x) =
      (Real.cos ((intervalFrequency ℓ m - intervalFrequency ℓ n) * x) -
        Real.cos ((intervalFrequency ℓ m + intervalFrequency ℓ n) * x)) / 2 := by
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos
      ((intervalFrequency ℓ m - intervalFrequency ℓ n) * x))).intervalIntegrable 0 ℓ.val)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos
      ((intervalFrequency ℓ m + intervalFrequency ℓ n) * x))).intervalIntegrable 0 ℓ.val),
    integral_cos_frequency_sub ℓ hmn, integral_cos_frequency_add ℓ hmn]
  norm_num

theorem integral_cos_frequency_mul_cos_frequency (ℓ : {ℓ : ℝ // 0 < ℓ}) {m n : ℕ}
    (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, Real.cos (intervalFrequency ℓ m * x) *
      Real.cos (intervalFrequency ℓ n * x)) = 0 := by
  have heq (x : ℝ) : Real.cos (intervalFrequency ℓ m * x) *
      Real.cos (intervalFrequency ℓ n * x) =
      (Real.cos ((intervalFrequency ℓ m - intervalFrequency ℓ n) * x) +
        Real.cos ((intervalFrequency ℓ m + intervalFrequency ℓ n) * x)) / 2 := by
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos
      ((intervalFrequency ℓ m - intervalFrequency ℓ n) * x))).intervalIntegrable 0 ℓ.val)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos
      ((intervalFrequency ℓ m + intervalFrequency ℓ n) * x))).intervalIntegrable 0 ℓ.val),
    integral_cos_frequency_sub ℓ hmn, integral_cos_frequency_add ℓ hmn]
  norm_num

theorem integral_dirichletIntervalMode_mul_of_ne (ℓ : {ℓ : ℝ // 0 < ℓ})
    {m n : ℕ+} (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, dirichletIntervalMode ℓ m x * dirichletIntervalMode ℓ n x) = 0 := by
  have hcast : (m : ℕ) ≠ (n : ℕ) := fun h => hmn (Subtype.ext h)
  have heq (x : ℝ) : dirichletIntervalMode ℓ m x * dirichletIntervalMode ℓ n x =
      (Real.sqrt (2 / ℓ.val) ^ 2) * (Real.sin (intervalFrequency ℓ m * x) *
        Real.sin (intervalFrequency ℓ n * x)) := by
    unfold dirichletIntervalMode
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, integral_sin_frequency_mul_sin_frequency ℓ hcast,
    mul_zero]

theorem integral_neumannIntervalMode_mul_of_ne (ℓ : {ℓ : ℝ // 0 < ℓ})
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in 0..ℓ.val, neumannIntervalMode ℓ m x * neumannIntervalMode ℓ n x) = 0 := by
  have heq (x : ℝ) : neumannIntervalMode ℓ m x * neumannIntervalMode ℓ n x =
      (neumannIntervalCoefficient ℓ m * neumannIntervalCoefficient ℓ n) *
        (Real.cos (intervalFrequency ℓ m * x) * Real.cos (intervalFrequency ℓ n * x)) := by
    unfold neumannIntervalMode
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, integral_cos_frequency_mul_cos_frequency ℓ hmn,
    mul_zero]

theorem inner_dirichletIntervalModeL2_of_ne (ℓ : {ℓ : ℝ // 0 < ℓ})
    {m n : ℕ+} (hmn : m ≠ n) :
    ⟪dirichletIntervalModeL2 ℓ m, dirichletIntervalModeL2 ℓ n⟫_ℂ = 0 := by
  rw [inner_dirichletIntervalModeL2, integral_dirichletIntervalMode_mul_of_ne ℓ hmn,
    Complex.ofReal_zero]

theorem inner_neumannIntervalModeL2_of_ne (ℓ : {ℓ : ℝ // 0 < ℓ})
    {m n : ℕ} (hmn : m ≠ n) :
    ⟪neumannIntervalModeL2 ℓ m, neumannIntervalModeL2 ℓ n⟫_ℂ = 0 := by
  rw [inner_neumannIntervalModeL2, integral_neumannIntervalMode_mul_of_ne ℓ hmn,
    Complex.ofReal_zero]

/-- Physical normalized sine modes form an orthonormal family. Completeness is separate. -/
theorem orthonormal_dirichletIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Orthonormal ℂ (dirichletIntervalModeL2 ℓ) := by
  constructor
  · exact norm_dirichletIntervalModeL2 ℓ
  · intro m n hmn
    exact inner_dirichletIntervalModeL2_of_ne ℓ hmn

/-- Physical normalized cosine modes, including zero, form an orthonormal family. -/
theorem orthonormal_neumannIntervalModeL2 (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Orthonormal ℂ (neumannIntervalModeL2 ℓ) := by
  constructor
  · exact norm_neumannIntervalModeL2 ℓ
  · intro m n hmn
    exact inner_neumannIntervalModeL2_of_ne ℓ hmn

end LiebThirring.TFCubes

end
