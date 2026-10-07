/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.FirstVariationPairing

/-! # Differentiation of the TF kinetic integral

Lieb–Simon (1977) II.10. Differentiation is along a literal affine
line of representatives. An integrable power of the sum dominates derivatives
on a fixed interval, including points where the initial density vanishes.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem kinetic_line_derivative_bound (u v t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    |(5 / 3 : ℝ) * (u + t * (v - u)) ^ ((2 : ℝ) / 3) * (v - u)| ≤
      (5 / 3 : ℝ) * 2 ^ ((2 : ℝ) / 3) * (u + v) ^ ((5 : ℝ) / 3) := by
  have hs : 0 ≤ u + v := add_nonneg hu hv
  have hd : |v - u| ≤ u + v := by rw [abs_le]; constructor <;> linarith
  have hl : |u + t * (v - u)| ≤ 2 * (u + v) := by
    calc
      _ ≤ |u| + |t * (v - u)| := abs_add_le _ _
      _ = u + |t| * |v - u| := by rw [abs_of_nonneg hu, abs_mul]
      _ ≤ u + 1 * (u + v) := by
        apply add_le_add_right
        exact mul_le_mul (abs_le.mpr ht) hd (abs_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  calc
    _ = (5 / 3 : ℝ) * |(u + t * (v - u)) ^ ((2 : ℝ) / 3)| * |v - u| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 3)]
    _ ≤ (5 / 3 : ℝ) * (2 * (u + v)) ^ ((2 : ℝ) / 3) * (u + v) := by
      apply mul_le_mul _ hd (abs_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.abs_rpow_le_abs_rpow _ _).trans
        (Real.rpow_le_rpow (abs_nonneg _) hl (by norm_num))
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs]
      have he : (u + v) ^ ((2 : ℝ) / 3) * (u + v) =
          (u + v) ^ ((5 : ℝ) / 3) := by
        rw [← Real.rpow_add_one' hs (by norm_num : (2 : ℝ) / 3 + 1 ≠ 0)]
        norm_num
      rw [mul_assoc, mul_assoc, he]
      ring

theorem hasDerivAt_integral_kinetic_line (ρ σ : TFDensity) :
    HasDerivAt (fun t : ℝ => ∫ x : Position,
      (ρ.val x + t * (σ.val x - ρ.val x)) ^ ((5 : ℝ) / 3))
      ((5 / 3 : ℝ) * ∫ x : Position,
        (ρ.val x) ^ ((2 : ℝ) / 3) * (σ.val x - ρ.val x)) 0 := by
  let F := fun (t : ℝ) (x : Position) =>
    (ρ.val x + t * (σ.val x - ρ.val x)) ^ ((5 : ℝ) / 3)
  let F' := fun (t : ℝ) (x : Position) =>
    (5 / 3 : ℝ) * (ρ.val x + t * (σ.val x - ρ.val x)) ^ ((2 : ℝ) / 3) *
      (σ.val x - ρ.val x)
  let B := fun x : Position => (5 / 3 : ℝ) * 2 ^ ((2 : ℝ) / 3) *
    ((tfDensityAdd ρ σ).val x) ^ ((5 : ℝ) / 3)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) volume := by
    intro t
    exact ((Lp.aestronglyMeasurable ρ.val).add
      (((Lp.aestronglyMeasurable σ.val).sub (Lp.aestronglyMeasurable ρ.val)).const_mul t)).aemeasurable.pow_const _ |>.aestronglyMeasurable
  have hdm : AEStronglyMeasurable (F' 0) volume := by
    dsimp [F']
    exact ((((Lp.aestronglyMeasurable ρ.val).add
      (((Lp.aestronglyMeasurable σ.val).sub (Lp.aestronglyMeasurable ρ.val)).const_mul 0)).aemeasurable.pow_const _).aestronglyMeasurable.const_mul _).mul
      ((Lp.aestronglyMeasurable σ.val).sub (Lp.aestronglyMeasurable ρ.val))
  have hbound : ∀ᵐ x ∂(volume : Measure Position), ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖F' t x‖ ≤ B x := by
    filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ,
      tfDensityAdd_coeFn ρ σ] with x hx hy ha
    intro t ht
    dsimp [F', B]
    rw [ha]
    exact kinetic_line_derivative_bound _ _ t hx hy ht
  have hdiff : ∀ᵐ x ∂(volume : Measure Position), ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x
    intro t _
    have h := (Real.hasDerivAt_rpow_const (x := ρ.val x + t * (σ.val x - ρ.val x))
      (p := (5 : ℝ) / 3) (Or.inr (by norm_num))).comp t
      ((hasDerivAt_const t (ρ.val x)).add
        ((hasDerivAt_id t).mul_const (σ.val x - ρ.val x)))
    convert h using 1 <;> norm_num [F, F', Function.comp_def, Pi.add_apply]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure Position)) (F := F) (F' := F') (bound := B)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas)
    (by simpa [F] using integrable_tfDensity_rpow_five_thirds ρ) hdm hbound
    ((integrable_tfDensity_rpow_five_thirds (tfDensityAdd ρ σ)).const_mul _) hdiff
  convert h.2 using 1
  dsimp [F']
  simp only [zero_mul, add_zero, mul_assoc]
  rw [integral_const_mul]

end LiebThirring.TFMinimizer

end
