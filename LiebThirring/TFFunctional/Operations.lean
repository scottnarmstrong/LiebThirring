/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Mass
public import LiebThirring.ThomasFermi.DensityMeasure

/-! # Addition and nonnegative multiplication of TF densities

These operations use the literal Lp operations on the carrier.

-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

/-- The zero density. -/
@[expose] noncomputable def tfZeroDensity : TFDensity :=
  ⟨0, by
    filter_upwards [Lp.coeFn_zero ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position)] with x hx
    simpa only [hx, Pi.zero_apply] using (le_refl (0 : ℝ)),
    (integrable_zero Position ℝ volume).congr
      (Lp.coeFn_zero ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position)).symm⟩

/-- Pointwise addition in the TF density carrier. -/
@[expose] noncomputable def tfDensityAdd (ρ σ : TFDensity) : TFDensity :=
  ⟨ρ.val + σ.val, by
    filter_upwards [Lp.coeFn_add ρ.val σ.val, ρ.property.1, σ.property.1] with x hx hρ hσ
    rw [hx]
    exact add_nonneg hρ hσ,
    (ρ.property.2.add σ.property.2).congr (Lp.coeFn_add ρ.val σ.val).symm⟩

theorem tfDensityAdd_coeFn (ρ σ : TFDensity) :
    (tfDensityAdd ρ σ).val =ᵐ[volume] fun x => ρ.val x + σ.val x :=
  Lp.coeFn_add ρ.val σ.val

theorem tfMass_tfDensityAdd (ρ σ : TFDensity) :
    tfMass (tfDensityAdd ρ σ) = tfMass ρ + tfMass σ := by
  unfold tfMass
  rw [integral_congr_ae (tfDensityAdd_coeFn ρ σ), integral_add ρ.property.2 σ.property.2]

/-- Nonnegative scalar multiplication in the TF density carrier. -/
@[expose] noncomputable def tfDensitySMul (b : ℝ≥0) (ρ : TFDensity) : TFDensity :=
  ⟨(b : ℝ) • ρ.val, by
    filter_upwards [Lp.coeFn_smul (b : ℝ) ρ.val, ρ.property.1] with x hx hρ
    rw [hx]
    exact mul_nonneg b.property hρ,
    (ρ.property.2.const_mul (b : ℝ)).congr (Lp.coeFn_smul (b : ℝ) ρ.val).symm⟩

theorem tfDensitySMul_coeFn (b : ℝ≥0) (ρ : TFDensity) :
    (tfDensitySMul b ρ).val =ᵐ[volume] fun x => (b : ℝ) * ρ.val x :=
  Lp.coeFn_smul (b : ℝ) ρ.val

theorem tfMass_tfDensitySMul (b : ℝ≥0) (ρ : TFDensity) :
    tfMass (tfDensitySMul b ρ) = (b : ℝ) * tfMass ρ := by
  unfold tfMass
  rw [integral_congr_ae (tfDensitySMul_coeFn b ρ), integral_const_mul]

theorem tfDensityMeasure_tfDensityAdd (ρ σ : TFDensity) :
    tfDensityMeasure (tfDensityAdd ρ σ) = tfDensityMeasure ρ + tfDensityMeasure σ := by
  unfold tfDensityMeasure
  calc
    _ = volume.withDensity (fun x => ENNReal.ofReal (ρ.val x) + ENNReal.ofReal (σ.val x)) := by
      apply withDensity_congr_ae
      filter_upwards [tfDensityAdd_coeFn ρ σ, ρ.property.1, σ.property.1] with x hx hρ hσ
      rw [hx, ENNReal.ofReal_add hρ hσ]
    _ = _ := withDensity_add_left
      (ENNReal.measurable_ofReal.comp (Lp.stronglyMeasurable ρ.val).measurable) _

end LiebThirring.TFFunctional

end
