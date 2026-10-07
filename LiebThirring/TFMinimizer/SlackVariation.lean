/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.Equation

/-! # Addition variations when the relaxed mass cap is slack

Complementary slackness sets the multiplier to zero; the
first variation then pairs nonnegatively with every positive TF density.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem tfFirstVariation_ae_nonneg_of_mass_lt {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ < (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    ∀ᵐ x ∂(volume : Measure Position), 0 ≤ tfFirstVariation a z R ρ x := by
  have hνr : 0 < (ν : ℝ) := lt_of_le_of_lt (tfMass_nonneg ρ) hmass
  have hν : 0 < ν := by exact_mod_cast hνr
  obtain ⟨μ, hμ, hslack⟩ := linear_mass_minimum ν hν (tfFirstVariation a z R ρ)
    (integrable_tfFirstVariation_pair a z R ρ) ρ hmass.le
    (integral_tfFirstVariation_le_of_relaxed_minimizer a ν z R ρ hmass.le hmin)
    (integral_tfFirstVariation_self_nonpos a ν z R ρ hmass.le hmin)
  have hμzero : (μ : ℝ) = 0 := (mul_eq_zero.mp hslack).resolve_right (sub_pos.mpr hmass).ne'
  filter_upwards [hμ] with x hx
  simpa only [hμzero, neg_zero] using hx.1

theorem integral_tfFirstVariation_pair_nonneg_of_mass_lt {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ < (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R)
    (σ : TFDensity) :
    0 ≤ ∫ x : Position, tfFirstVariation a z R ρ x * σ.val x := by
  apply integral_nonneg_of_ae
  filter_upwards [tfFirstVariation_ae_nonneg_of_mass_lt a ν z R ρ hmass hmin,
    tfDensity_ae_nonneg σ] with x hx hy
  exact mul_nonneg hx hy

end LiebThirring.TFMinimizer

end
