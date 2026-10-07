/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityBasic
public import LiebThirring.TFFunctional.Operations

/-! # Absolute differences of Thomas--Fermi densities -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- The pointwise absolute difference of two TF densities, retained as a TF density. -/
noncomputable def tfDensityAbsDiff (ρ σ : TFDensity) : TFDensity :=
  ⟨|ρ.val - σ.val|, by
    constructor
    · filter_upwards [Lp.coeFn_abs (ρ.val - σ.val)] with x hx
      rw [hx]
      exact abs_nonneg _
    · refine ((integrable_tfDensity ρ).sub (integrable_tfDensity σ)).norm.congr ?_
      filter_upwards [Lp.coeFn_abs (ρ.val - σ.val), Lp.coeFn_sub ρ.val σ.val] with x ha hs
      rw [ha, hs, Real.norm_eq_abs] ⟩

theorem tfDensityAbsDiff_apply_ae (ρ σ : TFDensity) :
    ∀ᵐ x ∂(volume : Measure Position),
      (tfDensityAbsDiff ρ σ).val x = |ρ.val x - σ.val x| := by
  filter_upwards [Lp.coeFn_abs (ρ.val - σ.val), Lp.coeFn_sub ρ.val σ.val] with x ha hs
  change (|ρ.val - σ.val| : Lp ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position)) x = _
  rw [ha, hs, Pi.sub_apply]

theorem tfMass_tfDensityAbsDiff (ρ σ : TFDensity) :
    tfMass (tfDensityAbsDiff ρ σ) = ∫ x : Position, |ρ.val x - σ.val x| := by
  unfold tfMass
  exact integral_congr_ae (tfDensityAbsDiff_apply_ae ρ σ)

theorem norm_tfDensityAbsDiff (ρ σ : TFDensity) :
    ‖(tfDensityAbsDiff ρ σ).val‖ = ‖ρ.val - σ.val‖ := by
  exact norm_abs_eq_norm _

theorem abs_tfMass_sub_le (ρ σ : TFDensity) :
    |tfMass ρ - tfMass σ| ≤ tfMass (tfDensityAbsDiff ρ σ) := by
  unfold tfMass
  rw [← integral_sub (integrable_tfDensity ρ) (integrable_tfDensity σ)]
  calc
    _ ≤ ∫ x : Position, |ρ.val x - σ.val x| := abs_integral_le_integral_abs
    _ = _ := (tfMass_tfDensityAbsDiff ρ σ).symm

theorem tfDensityMeasure_le_add_absDiff_left (ρ σ : TFDensity) :
    tfDensityMeasure ρ ≤ tfDensityMeasure (tfDensityAdd σ (tfDensityAbsDiff ρ σ)) := by
  unfold tfDensityMeasure
  apply withDensity_mono
  filter_upwards [tfDensityAdd_coeFn σ (tfDensityAbsDiff ρ σ),
    tfDensityAbsDiff_apply_ae ρ σ] with x ha hd
  rw [ha, hd]
  apply ENNReal.ofReal_le_ofReal
  linarith [le_abs_self (ρ.val x - σ.val x)]

theorem tfDensityMeasure_le_add_absDiff_right (ρ σ : TFDensity) :
    tfDensityMeasure σ ≤ tfDensityMeasure (tfDensityAdd ρ (tfDensityAbsDiff ρ σ)) := by
  unfold tfDensityMeasure
  apply withDensity_mono
  filter_upwards [tfDensityAdd_coeFn ρ (tfDensityAbsDiff ρ σ),
    tfDensityAbsDiff_apply_ae ρ σ] with x ha hd
  rw [ha, hd, abs_sub_comm]
  apply ENNReal.ofReal_le_ofReal
  linarith [le_abs_self (σ.val x - ρ.val x)]

end LiebThirring.TFFunctional

end
