/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.FunctionalDerivative
public import LiebThirring.TFMinimizer.MinimizingSequence

/-! # Variational inequality for an actual relaxed minimizer

Lieb–Simon (1977) II.10. Only actual nonnegative density mixtures are
used as competitors, and their masses stay below the prescribed cap.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem integral_tfFirstVariation_tfDensitySMul {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) (b : ℝ≥0) :
    (∫ x : Position, tfFirstVariation a z R ρ x * (tfDensitySMul b σ).val x) =
      (b : ℝ) * ∫ x : Position, tfFirstVariation a z R ρ x * σ.val x := by
  calc
    _ = ∫ x : Position, (b : ℝ) * (tfFirstVariation a z R ρ x * σ.val x) := by
      apply integral_congr_ae
      filter_upwards [tfDensitySMul_coeFn b σ] with x hx
      rw [hx]
      ring
    _ = _ := integral_const_mul _ _

theorem integral_tfFirstVariation_le_of_relaxed_minimizer {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R)
    (σ : TFDensity) (hσ : tfMass σ ≤ (ν : ℝ)) :
    (∫ x : Position, tfFirstVariation a z R ρ x * ρ.val x) ≤
      ∫ x : Position, tfFirstVariation a z R ρ x * σ.val x := by
  apply sub_nonneg.mp
  apply nonneg_derivative_of_right_min (hasDerivAt_tfAffineFunctional a z R ρ σ)
    (by norm_num : (0 : ℝ) < 1)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  let b : ℝ≥0 := ⟨1 - t, sub_nonneg.mpr ht'.2⟩
  let c : ℝ≥0 := ⟨t, ht'.1⟩
  have hm : tfMass (tfMixture b c ρ σ) ≤ (ν : ℝ) := by
    rw [tfMass_tfMixture]
    calc
      _ ≤ (b : ℝ) * (ν : ℝ) + (c : ℝ) * (ν : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hmass b.property)
          (mul_le_mul_of_nonneg_left hσ c.property)
      _ = _ := by
        change (1 - t) * (ν : ℝ) + t * (ν : ℝ) = (ν : ℝ)
        ring
  have hv : tfFunctional a z R ρ = (tfRelaxedEnergy a ν z R).toReal := by
    simpa only [EReal.toReal_coe] using congrArg EReal.toReal hmin
  rw [tfAffineFunctional_zero, tfAffineFunctional_eq_mixture a z R ρ σ t ht', hv]
  exact tfRelaxedEnergy_toReal_le_trial a ν z R (tfMixture b c ρ σ) hm

theorem integral_tfFirstVariation_self_nonpos {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    (∫ x : Position, tfFirstVariation a z R ρ x * ρ.val x) ≤ 0 := by
  have h := integral_tfFirstVariation_le_of_relaxed_minimizer a ν z R ρ hmass hmin
    (tfDensitySMul 0 ρ) (by rw [tfMass_tfDensitySMul]; simp)
  simpa only [integral_tfFirstVariation_tfDensitySMul, NNReal.coe_zero, zero_mul] using h

end LiebThirring.TFMinimizer

end
