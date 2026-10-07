/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.PotentialRegularity
public import LiebThirring.Electrostatics.Newton
import LiebThirring.Screening.Exterior
import all LiebThirring.Electrostatics.Basic
import all LiebThirring.Electrostatics.FaceMeasurePotential

/-! # Newton spherical averages for TF potentials

Lieb–Simon (1977) II.17. All shell averages are genuine finite real
integrals. The local mean value identity requires zero density measure in the
ball, and keeps the nuclear singular points outside that ball.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem integrable_tfDensity_potential_shell (ρ : TFDensity) (a : Position) (r : ℝ) :
    Integrable (fun x : Position => (coulombPotential (tfDensityMeasure ρ) x).toReal)
      (shell a r) := by
  apply Integrable.of_bound (measurable_tfDensity_potential ρ).aestronglyMeasurable
    ((8 * Real.pi * Real.sqrt 1) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ + tfMass ρ / 1)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hn : 0 ≤ (8 * Real.pi * Real.sqrt 1) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ + tfMass ρ / 1 :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (norm_nonneg ρ.val)) (div_nonneg (tfMass_nonneg ρ) zero_lt_one.le)
  simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (coulombPotential_tfDensityMeasure_le_norm ρ x 1 zero_lt_one)

theorem integral_tfDensity_potential_shell (ρ : TFDensity) (a : Position)
    (r : ℝ) (hr : 0 < r) :
    (∫ x : Position, (coulombPotential (tfDensityMeasure ρ) x).toReal ∂shell a r) =
      (cappedCoulombPotential (tfDensityMeasure ρ) r a).toReal := by
  rw [integral_toReal (f := coulombPotential (tfDensityMeasure ρ))
    (show AEMeasurable (coulombPotential (tfDensityMeasure ρ)) (shell a r) from
      measurable_coulombKernel.lintegral_prod_right.aemeasurable)
    (Filter.Eventually.of_forall (coulombPotential_tfDensityMeasure_lt_top ρ))]
  change (coulombEnergy (shell a r) (tfDensityMeasure ρ)).toReal = _
  rw [coulombEnergy_symm]
  congr 1
  change (∫⁻ y : Position, coulombPotential (shell a r) y ∂tfDensityMeasure ρ) =
    ∫⁻ y : Position, cappedCoulombKernel r a y ∂tfDensityMeasure ρ
  apply lintegral_congr
  intro y
  rw [coulombPotential_shell a hr y]
  simp only [cappedCoulombKernel, norm_sub_rev a y, max_comm]

theorem integrable_tfNuclearPotential_shell {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (a : Position) (r : ℝ) (hr : 0 < r) :
    Integrable (tfNuclearPotential z R) (shell a r) := by
  unfold tfNuclearPotential
  apply integrable_finsetSum
  intro k _
  have hf : coulombPotential (shell a r) (R k) < ⊤ := by
    rw [coulombPotential_shell a hr]
    exact ENNReal.inv_lt_top.mpr
      (ENNReal.ofReal_pos.mpr (hr.trans_le (le_max_right _ _)))
  simpa only [div_eq_mul_inv, norm_sub_rev (R k)] using
    (integrable_inverse_norm_of_potential_lt_top (shell a r) (R k) hf).const_mul (z k : ℝ)

theorem integral_tfNuclearPotential_shell {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (a : Position) (r : ℝ) (hr : 0 < r) :
    (∫ x : Position, tfNuclearPotential z R x ∂shell a r) =
      ∑ k, (z k : ℝ) / max ‖R k - a‖ r := by
  unfold tfNuclearPotential
  have hi : ∀ k : Fin M, Integrable (fun x : Position => (z k : ℝ) / ‖x - R k‖)
      (shell a r) := by
    intro k
    have hf : coulombPotential (shell a r) (R k) < ⊤ := by
      rw [coulombPotential_shell a hr]
      exact ENNReal.inv_lt_top.mpr
        (ENNReal.ofReal_pos.mpr (hr.trans_le (le_max_right _ _)))
    simpa only [div_eq_mul_inv, norm_sub_rev (R k)] using
      (integrable_inverse_norm_of_potential_lt_top (shell a r) (R k) hf).const_mul (z k : ℝ)
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [div_eq_mul_inv, norm_sub_rev _ (R k)]
  rw [integral_const_mul, integral_inverse_norm_eq_potential]
  · rw [coulombPotential_shell a hr, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (le_max_of_le_left (norm_nonneg _))]
  · rw [coulombPotential_shell a hr]
    exact ENNReal.inv_lt_top.mpr
      (ENNReal.ofReal_pos.mpr (hr.trans_le (le_max_right _ _)))

theorem cappedCoulombPotential_eq_of_ball_measure_zero (η : Measure Position)
    (a : Position) (r : ℝ) (hz : η (ball a r) = 0) :
    cappedCoulombPotential η r a = coulombPotential η a := by
  apply lintegral_congr_ae
  have hnot : ∀ᵐ y ∂η, y ∉ ball a r := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hz
  filter_upwards [hnot] with y hy
  have hd : r ≤ ‖a - y‖ := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
  simp only [cappedCoulombKernel, max_eq_right hd, coulombKernel]

theorem integral_screenedPotential_shell_eq {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (a : Position) (r : ℝ) (hr : 0 < r)
    (hR : ∀ k, r ≤ ‖R k - a‖) (hzero : tfDensityMeasure ρ (ball a r) = 0) :
    (∫ x : Position, (tfNuclearPotential z R x -
      (coulombPotential (tfDensityMeasure ρ) x).toReal) ∂shell a r) =
      tfNuclearPotential z R a - (coulombPotential (tfDensityMeasure ρ) a).toReal := by
  rw [integral_sub (integrable_tfNuclearPotential_shell z R a r hr)
      (integrable_tfDensity_potential_shell ρ a r),
    integral_tfNuclearPotential_shell z R a r hr, integral_tfDensity_potential_shell ρ a r hr,
    cappedCoulombPotential_eq_of_ball_measure_zero _ a r hzero]
  congr 1
  unfold tfNuclearPotential
  apply Finset.sum_congr rfl
  intro k _
  rw [max_eq_left (hR k), norm_sub_rev]

end LiebThirring.TFMinimizer

end
