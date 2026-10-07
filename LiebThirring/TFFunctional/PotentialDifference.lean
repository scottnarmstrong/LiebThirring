/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityDifference
public import LiebThirring.TFFunctional.FunctionalAlgebra
public import LiebThirring.TFFunctional.PotentialNorm

/-! # Difference bounds for Thomas--Fermi potentials and Coulomb energies -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem coulombEnergy_mono {μ μ' ν ν' : Measure Position}
    (hμ : μ ≤ μ') (hν : ν ≤ ν') : coulombEnergy μ ν ≤ coulombEnergy μ' ν' := by
  simp only [coulombEnergy_eq_lintegral]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, coulombKernel x y ∂ν' ∂μ :=
      lintegral_mono fun _ => lintegral_mono' hν le_rfl
    _ ≤ _ := lintegral_mono' hμ le_rfl

theorem tfCoulombEnergy_mono_of_measure_le (ρ ρ' σ σ' : TFDensity)
    (hρ : tfDensityMeasure ρ ≤ tfDensityMeasure ρ')
    (hσ : tfDensityMeasure σ ≤ tfDensityMeasure σ') :
    tfCoulombEnergy ρ σ ≤ tfCoulombEnergy ρ' σ' := by
  unfold tfCoulombEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact ENNReal.toReal_mono (coulombEnergy_tfDensity_lt_top ρ' σ').ne
    (coulombEnergy_mono hρ hσ)

/-- A symmetric, deliberately loose difference bound suitable for convergence. -/
theorem abs_tfCoulombEnergy_self_sub_le (ρ σ : TFDensity) :
    |tfCoulombEnergy ρ ρ - tfCoulombEnergy σ σ| ≤
      2 * tfCoulombEnergy σ (tfDensityAbsDiff ρ σ) +
      2 * tfCoulombEnergy ρ (tfDensityAbsDiff ρ σ) +
      2 * tfCoulombEnergy (tfDensityAbsDiff ρ σ) (tfDensityAbsDiff ρ σ) := by
  let δ := tfDensityAbsDiff ρ σ
  have hρ := tfDensityMeasure_le_add_absDiff_left ρ σ
  have hσ := tfDensityMeasure_le_add_absDiff_right ρ σ
  have hρE : tfCoulombEnergy ρ ρ ≤
      tfCoulombEnergy (tfDensityAdd σ δ) (tfDensityAdd σ δ) :=
    tfCoulombEnergy_mono_of_measure_le _ _ _ _ hρ hρ
  have hσE : tfCoulombEnergy σ σ ≤
      tfCoulombEnergy (tfDensityAdd ρ δ) (tfDensityAdd ρ δ) :=
    tfCoulombEnergy_mono_of_measure_le _ _ _ _ hσ hσ
  have hρδ := tfCoulombEnergy_nonneg ρ δ
  have hσδ := tfCoulombEnergy_nonneg σ δ
  have hδδ := tfCoulombEnergy_nonneg δ δ
  rw [tfCoulombEnergy_add_self] at hρE hσE
  rw [abs_le]
  constructor <;> dsimp [δ] at *
  · linarith
  · linarith

theorem tfCoulombEnergy_le_norm_mass (ρ σ : TFDensity) :
    tfCoulombEnergy ρ σ ≤
      ((8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖σ.val‖ + tfMass σ) * tfMass ρ / 2 := by
  have hcoef : 0 ≤ (8 * Real.pi) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg (by positivity) _
  have hη : 0 ≤ (8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖σ.val‖ + tfMass σ :=
    add_nonneg (mul_nonneg hcoef (norm_nonneg σ.val)) (tfMass_nonneg σ)
  apply tfCoulombEnergy_le_of_potential_le ρ σ _ hη
  intro x
  have hb : 8 * Real.pi * Real.sqrt 1 = 8 * Real.pi := by rw [Real.sqrt_one, mul_one]
  simpa only [hb, div_one] using coulombPotential_tfDensityMeasure_le_norm σ x 1 zero_lt_one

theorem abs_tfCoulombEnergy_self_sub_le_norm_mass (ρ σ : TFDensity) :
    |tfCoulombEnergy ρ ρ - tfCoulombEnergy σ σ| ≤
      ((8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖(tfDensityAbsDiff ρ σ).val‖ +
          tfMass (tfDensityAbsDiff ρ σ)) *
        (tfMass ρ + tfMass σ + tfMass (tfDensityAbsDiff ρ σ)) := by
  let δ := tfDensityAbsDiff ρ σ
  have hσ := tfCoulombEnergy_le_norm_mass σ δ
  have hρ := tfCoulombEnergy_le_norm_mass ρ δ
  have hδ := tfCoulombEnergy_le_norm_mass δ δ
  have hmain := abs_tfCoulombEnergy_self_sub_le ρ σ
  dsimp [δ] at hσ hρ hδ hmain ⊢
  have hcoef : 0 ≤ (8 * Real.pi) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ (8 * Real.pi) ^ ((2 : ℝ) / 5) *
      ‖(tfDensityAbsDiff ρ σ).val‖ + tfMass (tfDensityAbsDiff ρ σ) := by
    exact add_nonneg (mul_nonneg hcoef (norm_nonneg _))
      (tfMass_nonneg (tfDensityAbsDiff ρ σ))
  have hmρ := tfMass_nonneg ρ
  have hmσ := tfMass_nonneg σ
  have hmδ := tfMass_nonneg (tfDensityAbsDiff ρ σ)
  nlinarith

end LiebThirring.TFFunctional

end
