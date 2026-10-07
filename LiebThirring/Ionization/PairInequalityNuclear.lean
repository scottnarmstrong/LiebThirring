/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedRadial
public import LiebThirring.Variational.FormIntegral
public import LiebThirring.Variational.CompactMass
public import LiebThirring.Defs.Coulomb
public import LiebThirring.Kinetic.CurryingDensity

/-! # The cutoff attraction bound without a moment assumption -/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- Multiplication by the cutoff weight cancels the nuclear pole and is bounded by one. -/
theorem ionizationWeight_mul_inv_le_one {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    ionizationWeight ε r * r⁻¹ ≤ 1 := by
  by_cases h : r = 0
  · simp [h]
  have hd : 0 < 1 + ε * r := by positivity
  have he : ionizationWeight ε r * r⁻¹ = (1 + ε * r)⁻¹ := by
    unfold ionizationWeight
    field_simp
  rw [he]
  exact (inv_le_one₀ hd).mpr (le_add_of_nonneg_right (mul_nonneg hε hr))

/-- The selected weighted nuclear density lies between zero and `Z` times the mass density. -/
theorem ionization_nuclear_density_bounds {N q : ℕ} (i : Fin N) (Z : ℝ≥0)
    {ε : ℝ} (hε : 0 ≤ ε) (u : State N q) (X : Configuration N) :
    0 ≤ ionizationWeight ε ‖particlePosition X i‖ *
      ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal * ‖u X‖ ^ 2 ∧
    ionizationWeight ε ‖particlePosition X i‖ *
      ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal * ‖u X‖ ^ 2 ≤
      (Z : ℝ) * ‖u X‖ ^ 2 := by
  constructor
  · exact mul_nonneg (mul_nonneg (ionizationWeight_nonneg hε (norm_nonneg _))
      ENNReal.toReal_nonneg) (sq_nonneg _)
  · simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, coulombKernel,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _), sub_zero]
    calc
      _ = (Z : ℝ) * (ionizationWeight ε ‖particlePosition X i‖ *
          ‖particlePosition X i‖⁻¹) * ‖u X‖ ^ 2 := by ring
      _ ≤ (Z : ℝ) * 1 * ‖u X‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ionizationWeight_mul_inv_le_one hε (norm_nonneg _))
            Z.coe_nonneg) (sq_nonneg _)
      _ = _ := by rw [mul_one]

/-- The selected weighted attraction is integrable for every L² state. -/
theorem integrable_ionization_nuclear_density {N q : ℕ} (i : Fin N) (Z : ℝ≥0)
    {ε : ℝ} (hε : 0 ≤ ε) (u : State N q) :
    Integrable (fun X : Configuration N => ionizationWeight ε ‖particlePosition X i‖ *
      ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal * ‖u X‖ ^ 2) := by
  have hi := ((Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (Z : ℝ)
  apply hi.mono'
  · have hw : Measurable (fun X : Configuration N => ionizationWeight ε ‖particlePosition X i‖) :=
      ((lipschitzWith_ionizationWeight hε).continuous.measurable.comp (measurable_particlePosition i))
    have hk : Measurable (fun X : Configuration N =>
        ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal) :=
      (measurable_const.mul
        (((measurable_particlePosition i).sub measurable_const).norm.ennreal_ofReal.inv)).ennreal_toReal
    exact (hw.mul hk).aestronglyMeasurable.mul ((Lp.aestronglyMeasurable u).norm.pow 2)
  · filter_upwards with X
    rw [Real.norm_eq_abs, abs_of_nonneg (ionization_nuclear_density_bounds i Z hε u X).1]
    exact (ionization_nuclear_density_bounds i Z hε u X).2

/-- Each weighted nuclear expectation costs at most `Z` times the state mass. -/
theorem integral_ionization_nuclear_density_le {N q : ℕ} (i : Fin N) (Z : ℝ≥0)
    {ε : ℝ} (hε : 0 ≤ ε) (u : State N q) :
    (∫ X : Configuration N, ionizationWeight ε ‖particlePosition X i‖ *
      ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal * ‖u X‖ ^ 2) ≤
      (Z : ℝ) * ‖u‖ ^ 2 := by
  rw [← integral_state_norm_sq u, ← integral_const_mul]
  apply integral_mono (integrable_ionization_nuclear_density i Z hε u)
    (((Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (Z : ℝ))
  intro X
  exact (ionization_nuclear_density_bounds i Z hε u X).2

end LiebThirring
end
