/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.Convexity

/-! # Strict convexity at every nontrivial TF mixture

Lieb–Simon (1977) II.6--II.8, pp. 39--40. The strict scalar
power inequality is integrated on the actual density carrier. The Coulomb
part uses only its proved convexity.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

/-- Nonnegative linear combination in the TF carrier. -/
@[expose] noncomputable def tfMixture (b c : ℝ≥0) (ρ σ : TFDensity) : TFDensity :=
  tfDensityAdd (tfDensitySMul b ρ) (tfDensitySMul c σ)

theorem tfMixture_apply_ae (b c : ℝ≥0) (ρ σ : TFDensity) :
    (tfMixture b c ρ σ).val =ᵐ[volume]
      fun x : Position => (b : ℝ) * ρ.val x + (c : ℝ) * σ.val x := by
  filter_upwards [tfDensityAdd_coeFn (tfDensitySMul b ρ) (tfDensitySMul c σ),
    tfDensitySMul_coeFn b ρ, tfDensitySMul_coeFn c σ] with x ha hb hc
  rw [tfMixture, ha, hb, hc]

theorem tfMass_tfMixture (b c : ℝ≥0) (ρ σ : TFDensity) :
    tfMass (tfMixture b c ρ σ) = (b : ℝ) * tfMass ρ + (c : ℝ) * tfMass σ := by
  rw [tfMixture, tfMass_tfDensityAdd, tfMass_tfDensitySMul, tfMass_tfDensitySMul]

theorem tfCoulombEnergy_smul_smul (b c : ℝ≥0) (ρ σ : TFDensity) :
    tfCoulombEnergy (tfDensitySMul b ρ) (tfDensitySMul c σ) =
      (b : ℝ) * (c : ℝ) * tfCoulombEnergy ρ σ := by
  unfold tfCoulombEnergy
  rw [tfDensityMeasure_tfDensitySMul, tfDensityMeasure_tfDensitySMul,
    coulombEnergy_smul_left, coulombEnergy_smul_right,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  ring

theorem tfCoulombEnergy_tfMixture (b c : ℝ≥0) (ρ σ : TFDensity) :
    tfCoulombEnergy (tfMixture b c ρ σ) (tfMixture b c ρ σ) =
      (b : ℝ) ^ 2 * tfCoulombEnergy ρ ρ +
        2 * (b : ℝ) * (c : ℝ) * tfCoulombEnergy ρ σ +
        (c : ℝ) ^ 2 * tfCoulombEnergy σ σ := by
  rw [tfMixture, tfCoulombEnergy_add_self, tfCoulombEnergy_tfDensitySMul,
    tfCoulombEnergy_tfDensitySMul, tfCoulombEnergy_smul_smul]
  ring

theorem integral_attraction_tfMixture {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (b c : ℝ≥0) (ρ σ : TFDensity) :
    (∫ x : Position, tfNuclearPotential z R x * (tfMixture b c ρ σ).val x) =
      (b : ℝ) * (∫ x : Position, tfNuclearPotential z R x * ρ.val x) +
        (c : ℝ) * ∫ x : Position, tfNuclearPotential z R x * σ.val x := by
  rw [tfMixture, integral_tfNuclearPotential_mul_add,
    integral_tfNuclearPotential_mul_tfDensitySMul, integral_tfNuclearPotential_mul_tfDensitySMul]

end LiebThirring.TFMinimizer

end
