/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CoulombBounds

/-! # The TF near/far estimate expressed in the carrier norm

Used for the mass completion diffuse mass completion.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal
namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
    apply (ENNReal.toReal_le_toReal (by simp) (ENNReal.div_ne_top (by simp) (by norm_num))).mp
    rw [ENNReal.toReal_div]
    norm_num⟩


theorem lintegral_tfDensity_rpow_three_fifths_eq_norm (ρ : TFDensity) :
    (∫⁻ y : Position, ENNReal.ofReal (ρ.val y) ^ ((5 : ℝ) / 3) ∂volume) ^
        ((3 : ℝ) / 5) = ENNReal.ofReal ‖ρ.val‖ := by
  have hlin : (∫⁻ y : Position, ENNReal.ofReal (ρ.val y) ^ ((5 : ℝ) / 3) ∂volume) =
      ENNReal.ofReal (∫ y : Position, (ρ.val y)^((5:ℝ)/3) ∂volume) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_tfDensity_rpow_five_thirds ρ) (by
        filter_upwards [tfDensity_ae_nonneg ρ] with y hy
        exact Real.rpow_nonneg hy _)]
    apply lintegral_congr_ae
    filter_upwards [tfDensity_ae_nonneg ρ] with y hy
    rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num)]
  rw [hlin, integral_tfDensity_rpow_eq_norm]
  have hn0 : 0 ≤ ‖ρ.val‖ := norm_nonneg (E := Lp ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position)) ρ.val
  let n : ℝ := ‖ρ.val‖
  change ENNReal.ofReal (n ^ ((5:ℝ)/3)) ^ ((3:ℝ)/5) = ENNReal.ofReal n
  have hn : 0 ≤ n := by exact hn0
  rw [← ENNReal.ofReal_rpow_of_nonneg hn (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num

theorem coulombPotential_tfDensityMeasure_le_norm (ρ : TFDensity) (x : Position)
    (r : ℝ) (hr : 0 < r) :
    coulombPotential (tfDensityMeasure ρ) x ≤
      ENNReal.ofReal ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ +
        tfMass ρ / r) := by
  have h := coulombPotential_tfDensityMeasure_le ρ x r hr
  rw [lintegral_tfDensity_rpow_three_fifths_eq_norm] at h
  have hbase : 0 ≤ 8 * Real.pi * Real.sqrt r := by positivity
  have hC : 0 ≤ (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg hbase _
  have hfar : 0 ≤ 1 / r := by positivity
  have hn : 0 ≤ ‖ρ.val‖ := norm_nonneg ρ.val
  rw [ENNReal.ofReal_rpow_of_nonneg hbase (by norm_num),
    ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hfar,
    ← ENNReal.ofReal_add (mul_nonneg hC hn)
      (mul_nonneg hfar (tfMass_nonneg ρ))] at h
  convert h using 1
  congr 1
  ring

end LiebThirring.TFFunctional

end
