/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityMeasureScaling
public import LiebThirring.TFFunctional.CoulombAlgebra
public import LiebThirring.TFFunctional.DensityBasic
public import LiebThirring.ThomasFermi.CoulombEnergy

/-! # Coulomb scaling of Thomas--Fermi densities -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

theorem coulombEnergy_tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure (tfDensityDilation β A hβ hA ρ))
        (tfDensityMeasure (tfDensityDilation β A hβ hA σ)) =
      (ENNReal.ofReal A * ENNReal.ofReal ((β ^ 3)⁻¹)) ^ 2 *
        ENNReal.ofReal β * coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) := by
  let C := ENNReal.ofReal A * ENNReal.ofReal ((β ^ 3)⁻¹)
  rw [tfDensityMeasure_tfDensityDilation, tfDensityMeasure_tfDensityDilation,
    TFFunctional.coulombEnergy_smul_left,
    TFFunctional.coulombEnergy_smul_right,
    TFFunctional.coulombEnergy_map_smul β hβ]
  ring

theorem tfCoulombEnergy_tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ σ : TFDensity) :
    tfCoulombEnergy (tfDensityDilation β A hβ hA ρ)
        (tfDensityDilation β A hβ hA σ) =
      (A * (β ^ 3)⁻¹) ^ 2 * β * tfCoulombEnergy ρ σ := by
  unfold tfCoulombEnergy
  rw [coulombEnergy_tfDensityDilation β A hβ hA]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hβ.le 3)),
    ENNReal.toReal_ofReal hβ.le]
  ring

end LiebThirring

end
