/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.AttractionCoercivity

/-! # Uniform Thomas--Fermi coercivity on coefficient intervals -/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring.TFFunctional

/-- Explicit coercivity constant uniform for kinetic coefficients at least `amin`. -/
@[expose] noncomputable def uniformTFCoercivityConstant {M : ℕ}
    (amin : ℝ) (ν : ℝ≥0) (z : Fin M → ℝ≥0) : ℝ :=
  youngCoercivityConstant amin (attractionKineticCoefficient z) +
    totalNuclearCharge z * (ν : ℝ)

/-- Coercivity uniform over all coefficients bounded below by `amin`. -/
theorem tfFunctional_coercive_lower_bound_uniform {M : ℕ}
    (a : {a : ℝ // 0 < a}) {amin : ℝ} (hamin : 0 < amin) (hmina : amin ≤ a.val)
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ)) :
    a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
        uniformTFCoercivityConstant amin ν z ≤ tfFunctional a z R ρ := by
  apply tfFunctional_lower_bound_uniform_of_attraction_le a amin hamin hmina z R ρ
    (attractionKineticCoefficient z) (totalNuclearCharge z * (ν : ℝ))
    (integral_tfDensity_rpow_five_thirds_nonneg ρ)
    (attractionKineticCoefficient_nonneg z)
    ?_ (tfCoulombEnergy_nonneg ρ ρ)
  calc
    _ ≤ attractionKineticCoefficient z *
          (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        totalNuclearCharge z * tfMass ρ := integral_tfNuclearPotential_mul_le z R ρ
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left hmass (totalNuclearCharge_nonneg z)) _

end LiebThirring.TFFunctional

end
