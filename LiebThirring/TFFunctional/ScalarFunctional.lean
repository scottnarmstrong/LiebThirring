/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.FunctionalAlgebra

/-! # Exact amplitude scaling of the TF functional

These formulas retain the literal density carrier and the Coulomb factor 1/2.

-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal
namespace LiebThirring.TFFunctional

theorem tfDensityMeasure_tfDensitySMul (b : ℝ≥0) (ρ : TFDensity) :
    tfDensityMeasure (tfDensitySMul b ρ) = (b : ℝ≥0∞) • tfDensityMeasure ρ := by
  unfold tfDensityMeasure
  calc
    _ = volume.withDensity ((b : ℝ≥0∞) • fun x : Position => ENNReal.ofReal (ρ.val x)) := by
      apply withDensity_congr_ae
      filter_upwards [tfDensitySMul_coeFn b ρ] with x hx
      rw [hx]
      change ENNReal.ofReal ((b : ℝ) * ρ.val x) =
        (b : ℝ≥0∞) * ENNReal.ofReal (ρ.val x)
      exact (ENNReal.ofReal_mul b.property).trans
        (congrArg (fun c : ℝ≥0∞ => c * ENNReal.ofReal (ρ.val x))
          (ENNReal.ofReal_coe_nnreal (p := b)))
    _ = _ := withDensity_smul' _ _ ENNReal.coe_ne_top

theorem integral_tfNuclearPotential_mul_tfDensitySMul {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (b : ℝ≥0) (ρ : TFDensity) :
    (∫ x : Position, tfNuclearPotential z R x * (tfDensitySMul b ρ).val x) =
      (b : ℝ) * ∫ x : Position, tfNuclearPotential z R x * ρ.val x := by
  calc
    _ = ∫ x : Position, (b : ℝ) * (tfNuclearPotential z R x * ρ.val x) := by
      apply integral_congr_ae
      filter_upwards [tfDensitySMul_coeFn b ρ] with x hx
      rw [hx]
      ring
    _ = _ := integral_const_mul _ _

theorem tfCoulombEnergy_tfDensitySMul (b : ℝ≥0) (ρ σ : TFDensity) :
    tfCoulombEnergy (tfDensitySMul b ρ) (tfDensitySMul b σ) =
      (b : ℝ) ^ 2 * tfCoulombEnergy ρ σ := by
  unfold tfCoulombEnergy
  rw [tfDensityMeasure_tfDensitySMul, tfDensityMeasure_tfDensitySMul,
    coulombEnergy_smul_left, coulombEnergy_smul_right,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  ring

end LiebThirring.TFFunctional

end
