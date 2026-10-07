/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.ScalingTerms
public import LiebThirring.TFFunctional.CoulombScaling

/-! # Exact scaling of the Thomas--Fermi functional -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The natural three-dimensional dilation scales every term of the TF functional
by the seventh power of the inverse length scale. -/
theorem tfFunctional_tfDensityDilation {M : ℕ} (a : {a : ℝ // 0 < a})
    (β : ℝ) (hβ : 0 < β) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) :
    tfFunctional a (fun k => (Real.toNNReal β) ^ (3 : ℕ) * z k)
        (fun k => β⁻¹ • R k)
        (tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ) =
      β ^ 7 * tfFunctional a z R ρ := by
  unfold tfFunctional
  rw [integral_rpow_tfDensityDilation β (β ^ 6) hβ (pow_pos hβ 6),
    integral_tfNuclearPotential_mul_tfDensityDilation β (β ^ 6)
      ((Real.toNNReal β) ^ (3 : ℕ)) hβ (pow_nonneg hβ.le 6) z R ρ,
    tfCoulombEnergy_tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6)]
  have hrpow : (β ^ 6) ^ ((5 : ℝ) / 3) = β ^ 10 := by
    rw [← Real.rpow_natCast_mul hβ.le 6]
    convert Real.rpow_natCast β 10 using 1
    all_goals norm_num
  rw [hrpow]
  simp only [NNReal.coe_pow, Real.coe_toNNReal β hβ.le]
  field_simp [hβ.ne']

end LiebThirring

end
