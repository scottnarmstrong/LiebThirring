/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.EulerInequality
public import LiebThirring.TFMinimizer.LinearMassMinimum

/-! # TF equation and complementary slackness

The relaxed minimizer satisfies the screened-potential equation. Source: Lieb–Simon (1977) II.10, pp. 40--43. The multiplier comes from first variations
of the actual relaxed minimizer. No minimizer mass is used as a denominator.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

/-- The TF equation for the actual relaxed minimizer, with the mass-cap KKT condition. -/
theorem tfEquation_of_relaxed_minimizer {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    ∃ μ : ℝ≥0,
      (∀ᵐ x ∂(volume : Measure Position),
        (5 / 3 : ℝ) * a.val * (ρ.val x) ^ ((2 : ℝ) / 3) =
          max (tfNuclearPotential z R x -
            (coulombPotential (tfDensityMeasure ρ) x).toReal - (μ : ℝ)) 0) ∧
      (μ : ℝ) * ((ν : ℝ) - tfMass ρ) = 0 := by
  have _source_data : (∀ k, 0 < z k) ∧ Function.Injective R := ⟨hz, hR⟩
  obtain ⟨μ, hμ, hslack⟩ := linear_mass_minimum ν hν (tfFirstVariation a z R ρ)
    (integrable_tfFirstVariation_pair a z R ρ) ρ hmass
    (integral_tfFirstVariation_le_of_relaxed_minimizer a ν z R ρ hmass hmin)
    (integral_tfFirstVariation_self_nonpos a ν z R ρ hmass hmin)
  refine ⟨μ, ?_, hslack⟩
  filter_upwards [hμ, tfDensity_ae_nonneg ρ] with x hx hρ
  have hkin : 0 ≤ (5 / 3 : ℝ) * a.val * (ρ.val x) ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (by norm_num) a.property.le) (Real.rpow_nonneg hρ _)
  dsimp only [tfFirstVariation] at hx
  by_cases hzero : ρ.val x = 0
  · have hk : (5 / 3 : ℝ) * a.val * (ρ.val x) ^ ((2 : ℝ) / 3) = 0 := by
      rw [hzero, Real.zero_rpow (by norm_num : (2 : ℝ) / 3 ≠ 0), mul_zero]
    rw [hk, max_eq_right (by linarith [hx.1, hk])]
  · have he := (mul_eq_zero.mp hx.2).resolve_right hzero
    rw [max_eq_left (by linarith only [he, hkin])]
    linarith only [he]

end LiebThirring.TFMinimizer

end
