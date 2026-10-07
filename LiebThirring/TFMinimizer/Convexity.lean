/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.KineticEstimate
public import LiebThirring.TFFunctional.ScalarFunctional

/-! # Quantitative midpoint convexity of the TF functional

Coulomb positivity is used on positive density
measures; no signed difference is presented as a nonnegative TF density.
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

/-- Midpoint in the literal TF density carrier. -/
@[expose] noncomputable def tfMidpoint (ρ σ : TFDensity) : TFDensity :=
  tfDensitySMul (1 / 2 : ℝ≥0) (tfDensityAdd ρ σ)

theorem tfMidpoint_apply_ae (ρ σ : TFDensity) :
    (tfMidpoint ρ σ).val =ᵐ[volume] fun x : Position => (ρ.val x + σ.val x) / 2 := by
  filter_upwards [tfDensitySMul_coeFn (1 / 2 : ℝ≥0) (tfDensityAdd ρ σ),
    tfDensityAdd_coeFn ρ σ] with x hm ha
  rw [tfMidpoint, hm, ha]
  norm_num
  ring

theorem tfMass_tfMidpoint (ρ σ : TFDensity) :
    tfMass (tfMidpoint ρ σ) = (tfMass ρ + tfMass σ) / 2 := by
  rw [tfMidpoint, tfMass_tfDensitySMul, tfMass_tfDensityAdd]
  norm_num
  ring

theorem tfCoulombEnergy_two_mul_le (ρ σ : TFDensity) :
    2 * tfCoulombEnergy ρ σ ≤ tfCoulombEnergy ρ ρ + tfCoulombEnergy σ σ := by
  have haa := (coulombEnergy_tfDensity_lt_top ρ ρ).ne
  have hbb := (coulombEnergy_tfDensity_lt_top σ σ).ne
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨haa, hbb⟩)
    (two_mul_coulombEnergy_le (tfDensityMeasure ρ) (tfDensityMeasure σ) haa hbb)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add haa hbb] at h
  norm_num at h
  unfold tfCoulombEnergy
  linarith

theorem tfCoulombEnergy_tfMidpoint_le (ρ σ : TFDensity) :
    tfCoulombEnergy (tfMidpoint ρ σ) (tfMidpoint ρ σ) ≤
      (tfCoulombEnergy ρ ρ + tfCoulombEnergy σ σ) / 2 := by
  rw [tfMidpoint, tfCoulombEnergy_tfDensitySMul, tfCoulombEnergy_add_self]
  have h := tfCoulombEnergy_two_mul_le ρ σ
  norm_num
  linarith

theorem integral_kineticWeight_le_midpoint_defect (ρ σ : TFDensity) :
    (5 / 36 : ℝ) * (∫ x : Position, kineticWeight ρ σ x) ≤
      ((∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) +
        ∫ x : Position, (σ.val x) ^ ((5 : ℝ) / 3)) / 2 -
      ∫ x : Position, ((tfMidpoint ρ σ).val x) ^ ((5 : ℝ) / 3) := by
  have hρ := integrable_tfDensity_rpow_five_thirds ρ
  have hσ := integrable_tfDensity_rpow_five_thirds σ
  have hm := integrable_tfDensity_rpow_five_thirds (tfMidpoint ρ σ)
  have hadd : Integrable (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3) +
      (σ.val x) ^ ((5 : ℝ) / 3)) volume := hρ.add hσ
  have hdiv : Integrable (fun x : Position => ((ρ.val x) ^ ((5 : ℝ) / 3) +
      (σ.val x) ^ ((5 : ℝ) / 3)) / 2) volume := hadd.div_const 2
  calc
    _ = ∫ x : Position, (5 / 36 : ℝ) * kineticWeight ρ σ x := (integral_const_mul _ _).symm
    _ ≤ ∫ x : Position, ((ρ.val x) ^ ((5 : ℝ) / 3) +
        (σ.val x) ^ ((5 : ℝ) / 3)) / 2 -
        ((tfMidpoint ρ σ).val x) ^ ((5 : ℝ) / 3) := by
      apply integral_mono_ae ((integrable_kineticWeight ρ σ).const_mul _)
        (hdiv.sub hm)
      filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ,
        tfMidpoint_apply_ae ρ σ] with x hx hy hm
      dsimp only [Pi.sub_apply]
      rw [hm]
      simpa only [kineticWeight, mul_div_assoc] using
        rpow_five_thirds_midpoint_defect _ _ hx hy
    _ = _ := by rw [integral_sub hdiv hm,
      integral_div, integral_add hρ hσ]

/-- Uniform positive control of the squared L5/3 difference on a norm ball. -/
theorem tfFunctional_midpoint_defect_controls_norm {M : ℕ}
    (a : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (B : ℝ) (hB : 0 < B) (ρ σ : TFDensity)
    (hρ : ‖ρ.val‖ ≤ B) (hσ : ‖σ.val‖ ≤ B) :
    ((5 / 36 : ℝ) * a.val / (2 * B) ^ ((1 : ℝ) / 3)) * ‖ρ.val - σ.val‖ ^ 2 ≤
      (tfFunctional a z R ρ + tfFunctional a z R σ) / 2 -
        tfFunctional a z R (tfMidpoint ρ σ) := by
  let C := (2 * B) ^ ((1 : ℝ) / 3)
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  have hsum : ‖ρ.val + σ.val‖ ≤ 2 * B := by
    exact (norm_add_le _ _).trans (by linarith)
  have hn := (norm_sub_sq_le_integral_kineticWeight ρ σ).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hsum (by norm_num))
      (integral_nonneg_of_ae (kineticWeight_ae_nonneg ρ σ)))
  have hk := integral_kineticWeight_le_midpoint_defect ρ σ
  have hc := tfCoulombEnergy_tfMidpoint_le ρ σ
  have hv : (∫ x : Position, tfNuclearPotential z R x * (tfMidpoint ρ σ).val x) =
      ((∫ x : Position, tfNuclearPotential z R x * ρ.val x) +
        ∫ x : Position, tfNuclearPotential z R x * σ.val x) / 2 := by
    rw [tfMidpoint, integral_tfNuclearPotential_mul_tfDensitySMul,
      integral_tfNuclearPotential_mul_add]
    norm_num
    ring
  have hd : (5 / 36 : ℝ) * a.val * (∫ x : Position, kineticWeight ρ σ x) ≤
      (tfFunctional a z R ρ + tfFunctional a z R σ) / 2 -
        tfFunctional a z R (tfMidpoint ρ σ) := by
    have hk' := mul_le_mul_of_nonneg_left hk a.property.le
    unfold tfFunctional
    rw [hv]
    nlinarith only [hk', hc]
  change ((5 / 36 : ℝ) * a.val / C) * _ ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have hn' := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 36) a.property.le)
  have hd' := mul_le_mul_of_nonneg_right hd hC.le
  dsimp [C] at *
  nlinarith only [hn', hd']

/-- Distinct TF densities have a strictly positive midpoint defect. -/
theorem tfFunctional_tfMidpoint_lt {M : ℕ}
    (a : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ σ : TFDensity) (hne : ρ ≠ σ) :
    tfFunctional a z R (tfMidpoint ρ σ) <
      (tfFunctional a z R ρ + tfFunctional a z R σ) / 2 := by
  let B := ‖ρ.val‖ + ‖σ.val‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have h := tfFunctional_midpoint_defect_controls_norm a z R B hB ρ σ
    (by dsimp [B]; linarith [norm_nonneg σ.val])
    (by dsimp [B]; linarith [norm_nonneg ρ.val])
  have hn : 0 < ‖ρ.val - σ.val‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (fun heq => hne (Subtype.ext heq)))
  have hp : 0 < ((5 / 36 : ℝ) * a.val / (2 * B) ^ ((1 : ℝ) / 3)) *
      ‖ρ.val - σ.val‖ ^ 2 := mul_pos
    (div_pos (mul_pos (by norm_num) a.property)
      (Real.rpow_pos_of_pos (by positivity) _)) (sq_pos_of_pos hn)
  linarith

end LiebThirring.TFMinimizer

end
