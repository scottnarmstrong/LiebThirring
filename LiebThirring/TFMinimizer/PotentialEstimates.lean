/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Continuity
import all LiebThirring.Electrostatics.Basic

/-! # Adjustable-radius interaction estimates

The TF finiteness estimates near/far estimate is applied to the absolute difference. This is the
bounded-mass strong-Lp continuity route used for the relaxed minimization.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem tfMass_absDiff_le (ρ σ : TFDensity) :
    tfMass (tfDensityAbsDiff ρ σ) ≤ tfMass ρ + tfMass σ := by
  rw [tfMass_tfDensityAbsDiff]
  unfold tfMass
  rw [← integral_add (integrable_tfDensity ρ) (integrable_tfDensity σ)]
  apply integral_mono_ae
    ((integrable_tfDensity ρ).sub (integrable_tfDensity σ)).abs
    ((integrable_tfDensity ρ).add (integrable_tfDensity σ))
  filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ] with x hρ hσ
  dsimp
  rw [abs_le]
  constructor <;> linarith

/-- The real one-centre attraction integral equals the finite potential. -/
theorem integral_inv_norm_mul_eq_potential (ρ : TFDensity) (x : Position) :
    (∫ y : Position, ‖y - x‖⁻¹ * ρ.val y) =
      (coulombPotential (tfDensityMeasure ρ) x).toReal := by
  have hi := integrable_inv_norm_mul_tfDensity ρ x
  have hn : ∀ᵐ y ∂(volume : Measure Position), 0 ≤ ‖y - x‖⁻¹ * ρ.val y := by
    filter_upwards [tfDensity_ae_nonneg ρ] with y hy
    positivity
  have he : ENNReal.ofReal (∫ y : Position, ‖y - x‖⁻¹ * ρ.val y) =
      coulombPotential (tfDensityMeasure ρ) x := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hn]
    unfold coulombPotential tfDensityMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (measurable_coulombKernel_right x)]
    apply lintegral_congr_ae
    filter_upwards [(volume : Measure Position).ae_ne x, tfDensity_ae_nonneg ρ] with y hxy hy
    change ENNReal.ofReal (‖y - x‖⁻¹ * ρ.val y) =
      ENNReal.ofReal (ρ.val y) * (ENNReal.ofReal ‖x - y‖)⁻¹
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)),
      ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)),
      norm_sub_rev, mul_comm]
  rw [← he, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae hn

theorem integral_tfNuclearPotential_mul_eq_sum_potential {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) :
    (∫ x : Position, tfNuclearPotential z R x * ρ.val x) =
      ∑ k, (z k : ℝ) * (coulombPotential (tfDensityMeasure ρ) (R k)).toReal := by
  unfold tfNuclearPotential
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (integrable_inv_norm_mul_tfDensity ρ (R k)).const_mul (z k : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_inv_norm_mul_eq_potential, ← integral_const_mul]
  congr 1
  funext x
  simp only [div_eq_mul_inv]
  ring

theorem integral_tfNuclearPotential_mul_le_radius {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity)
    (r : ℝ) (hr : 0 < r) :
    (∫ x : Position, tfNuclearPotential z R x * ρ.val x) ≤
      totalNuclearCharge z *
        ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ + tfMass ρ / r) := by
  rw [integral_tfNuclearPotential_mul_eq_sum_potential]
  unfold totalNuclearCharge
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (z k).property
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (coulombPotential_tfDensityMeasure_le_norm ρ (R k) r hr)
  have hC : 0 ≤ (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg (by positivity) _
  rwa [ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hC (norm_nonneg ρ.val))
    (div_nonneg (tfMass_nonneg ρ) hr.le))] at h

theorem abs_attraction_sub_le_radius {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity)
    (r : ℝ) (hr : 0 < r) :
    |(∫ x : Position, tfNuclearPotential z R x * ρ.val x) -
      ∫ x : Position, tfNuclearPotential z R x * σ.val x| ≤
      totalNuclearCharge z *
        ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val - σ.val‖ +
          (tfMass ρ + tfMass σ) / r) := by
  let δ := tfDensityAbsDiff ρ σ
  have hiρ := integrable_tfNuclearPotential_mul z R ρ
  have hiσ := integrable_tfNuclearPotential_mul z R σ
  have heq : (fun x : Position => |tfNuclearPotential z R x * ρ.val x -
      tfNuclearPotential z R x * σ.val x|) =ᵐ[volume]
      fun x => tfNuclearPotential z R x * δ.val x := by
    filter_upwards [tfDensityAbsDiff_apply_ae ρ σ] with x hx
    rw [hx, ← mul_sub, abs_mul, abs_of_nonneg (tfNuclearPotential_nonneg z R x)]
  calc
    _ = |∫ x : Position, (tfNuclearPotential z R x * ρ.val x -
        tfNuclearPotential z R x * σ.val x)| := by rw [integral_sub hiρ hiσ]
    _ ≤ ∫ x : Position, |tfNuclearPotential z R x * ρ.val x -
        tfNuclearPotential z R x * σ.val x| := abs_integral_le_integral_abs
    _ = ∫ x : Position, tfNuclearPotential z R x * δ.val x := integral_congr_ae heq
    _ ≤ _ := by
      apply (integral_tfNuclearPotential_mul_le_radius z R δ r hr).trans
      rw [norm_tfDensityAbsDiff]
      apply mul_le_mul_of_nonneg_left _ (totalNuclearCharge_nonneg z)
      apply add_le_add_right
      exact div_le_div_of_nonneg_right (tfMass_absDiff_le ρ σ) hr.le

theorem abs_coulomb_self_sub_le_radius (ρ σ : TFDensity)
    (r : ℝ) (hr : 0 < r) :
    |tfCoulombEnergy ρ ρ - tfCoulombEnergy σ σ| ≤
      2 * (tfMass ρ + tfMass σ) *
        ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val - σ.val‖ +
          (tfMass ρ + tfMass σ) / r) := by
  let δ := tfDensityAbsDiff ρ σ
  let η := (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val - σ.val‖ +
    (tfMass ρ + tfMass σ) / r
  have hη : 0 ≤ η := by
    dsimp [η]
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (norm_nonneg (ρ.val - σ.val)))
      (div_nonneg (add_nonneg (tfMass_nonneg ρ) (tfMass_nonneg σ)) hr.le)
  have hp : ∀ x, coulombPotential (tfDensityMeasure δ) x ≤ ENNReal.ofReal η := by
    intro x
    apply (coulombPotential_tfDensityMeasure_le_norm δ x r hr).trans
    apply ENNReal.ofReal_le_ofReal
    rw [norm_tfDensityAbsDiff]
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (tfMass_absDiff_le ρ σ) hr.le
  have hρ := tfCoulombEnergy_le_of_potential_le ρ δ η hη hp
  have hσ := tfCoulombEnergy_le_of_potential_le σ δ η hη hp
  have hδ := tfCoulombEnergy_le_of_potential_le δ δ η hη hp
  have hm := mul_le_mul_of_nonneg_left (tfMass_absDiff_le ρ σ) hη
  have h := abs_tfCoulombEnergy_self_sub_le ρ σ
  change _ ≤ 2 * (tfMass ρ + tfMass σ) * η
  dsimp [δ] at hρ hσ hδ hm
  nlinarith only [hρ, hσ, hδ, hm, h]

end LiebThirring.TFMinimizer

end
