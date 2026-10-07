/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityBasic
public import LiebThirring.Assembly.CutoffRadial
public import LiebThirring.Electrostatics.FaceMeasureDecay
import all LiebThirring.Electrostatics.Basic

/-! # Near--far bounds for Thomas--Fermi Coulomb potentials -/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

private theorem holder_five_halves_five_thirds :
    Real.HolderConjugate ((5 : ℝ) / 2) ((5 : ℝ) / 3) :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

theorem lintegral_coulombKernel_rpow_ball (x : Position) (r : ℝ) (hr : 0 < r) :
    ∫⁻ y in ball x r, coulombKernel x y ^ ((5 : ℝ) / 2) ∂volume =
      ENNReal.ofReal (8 * Real.pi * Real.sqrt r) := by
  rw [show (∫⁻ y in ball x r, coulombKernel x y ^ ((5 : ℝ) / 2) ∂volume) =
      ∫⁻ y : Position,
        (if ‖y - x‖ < r then (ENNReal.ofReal ‖y - x‖)⁻¹ else 0) ^ ((5 : ℝ) / 2)
        ∂volume by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    apply lintegral_congr
    intro y
    simp only [indicator, mem_ball, dist_eq_norm, coulombKernel]
    split_ifs with h
    · rw [norm_sub_rev]
    · simp only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 5 / 2)] ]
  rw [lintegral_sub_right_eq_self
    (fun y : Position =>
      (if ‖y‖ < r then (ENNReal.ofReal ‖y‖)⁻¹ else 0) ^ ((5 : ℝ) / 2)) x]
  exact Assembly.lintegral_ball_inv_rpow r hr

theorem lintegral_tfDensity_rpow_lt_top (ρ : TFDensity) :
    (∫⁻ x : Position, ENNReal.ofReal (ρ.val x) ^ ((5 : ℝ) / 3) ∂volume) < ⊤ := by
  have hi := (integrable_tfDensity_rpow_five_thirds ρ).hasFiniteIntegral
  apply lt_of_le_of_lt ?_ hi
  apply lintegral_mono_ae
  filter_upwards [tfDensity_ae_nonneg ρ] with x hx
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hx _),
    ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

theorem coulombPotential_tfDensityMeasure_le (ρ : TFDensity) (x : Position)
    (r : ℝ) (hr : 0 < r) :
    coulombPotential (tfDensityMeasure ρ) x ≤
      (ENNReal.ofReal (8 * Real.pi * Real.sqrt r)) ^ ((2 : ℝ) / 5) *
          (∫⁻ y : Position, ENNReal.ofReal (ρ.val y) ^ ((5 : ℝ) / 3) ∂volume) ^
            ((3 : ℝ) / 5) +
        ENNReal.ofReal (1 / r) * ENNReal.ofReal (tfMass ρ) := by
  rw [show coulombPotential (tfDensityMeasure ρ) x =
      ∫⁻ y, coulombKernel x y ∂tfDensityMeasure ρ from rfl]
  rw [show tfDensityMeasure ρ =
      volume.withDensity (fun y : Position => ENNReal.ofReal (ρ.val y)) from rfl]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (measurable_coulombKernel_right x)]
  rw [← lintegral_add_compl _ (Metric.isOpen_ball.measurableSet : MeasurableSet (ball x r))]
  apply add_le_add
  · have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict (ball x r)) holder_five_halves_five_thirds
      (measurable_coulombKernel_right x).aemeasurable
      (Lp.memLp ρ.val).aemeasurable.ennreal_ofReal.restrict
    rw [lintegral_coulombKernel_rpow_ball x r hr] at hh
    have hfinal := hh.trans (mul_le_mul_of_nonneg_left
      (ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
        (by norm_num)) bot_le)
    convert hfinal using 1 <;> norm_num [Pi.mul_apply, mul_comm]
  · calc
      _ ≤ ∫⁻ y in (ball x r)ᶜ,
          ENNReal.ofReal (1 / r) * ENNReal.ofReal (ρ.val y) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with y hy
        have hk := coulombKernel_le_of_le_norm_sub x y hr (by
          simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, norm_sub_rev] using hy)
        change ENNReal.ofReal (ρ.val y) * coulombKernel x y ≤ _
        calc
          _ ≤ ENNReal.ofReal (ρ.val y) * ENNReal.ofReal (1 / r) :=
            mul_le_mul_of_nonneg_left hk bot_le
          _ = _ := mul_comm _ _
      _ ≤ ∫⁻ y : Position,
          ENNReal.ofReal (1 / r) * ENNReal.ofReal (ρ.val y) ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (1 / r) * ∫⁻ y : Position,
          ENNReal.ofReal (ρ.val y) ∂volume :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tfDensity ρ)
          (tfDensity_ae_nonneg ρ)]
        rfl

theorem coulombPotential_tfDensityMeasure_lt_top (ρ : TFDensity) (x : Position) :
    coulombPotential (tfDensityMeasure ρ) x < ⊤ := by
  have h := coulombPotential_tfDensityMeasure_le ρ x 1 zero_lt_one
  apply h.trans_lt
  apply ENNReal.add_lt_top.2
  constructor
  · apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (8 * Real.pi * Real.sqrt 1) ≠ ⊤)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lintegral_tfDensity_rpow_lt_top ρ).ne
  · exact ENNReal.mul_lt_top (by simp) (by simp)

theorem coulombEnergy_tfDensity_lt_top (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) < ⊤ := by
  let C : ℝ≥0∞ :=
    (ENNReal.ofReal (8 * Real.pi * Real.sqrt 1)) ^ ((2 : ℝ) / 5) *
        (∫⁻ y : Position, ENNReal.ofReal (σ.val y) ^ ((5 : ℝ) / 3) ∂volume) ^
          ((3 : ℝ) / 5) + ENNReal.ofReal (tfMass σ)
  have hC : C < ⊤ := by
    dsimp [C]
    apply ENNReal.add_lt_top.2
    constructor
    · apply ENNReal.mul_lt_top
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (ENNReal.ofReal_ne_top : ENNReal.ofReal (8 * Real.pi * Real.sqrt 1) ≠ ⊤)
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (lintegral_tfDensity_rpow_lt_top σ).ne
    · exact ENNReal.ofReal_lt_top
  unfold coulombEnergy
  calc
    (∫⁻ x, coulombPotential (tfDensityMeasure σ) x ∂tfDensityMeasure ρ) ≤
        ∫⁻ _x, C ∂tfDensityMeasure ρ := by
      apply lintegral_mono
      intro x
      simpa only [C, one_div, inv_one, ENNReal.ofReal_one, one_mul] using
        coulombPotential_tfDensityMeasure_le σ x 1 zero_lt_one
    _ = C * tfDensityMeasure ρ univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top hC (measure_lt_top _ _)

end LiebThirring.TFFunctional

end
