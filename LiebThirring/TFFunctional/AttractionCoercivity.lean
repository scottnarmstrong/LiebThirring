/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DomainFinite
public import LiebThirring.TFFunctional.Coercivity
public import LiebThirring.TFFunctional.EnergyFinite
import all LiebThirring.Electrostatics.Basic

/-! # Nuclear attraction bounds and concrete TF coercivity -/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

/-- The total molecular nuclear charge as a real number. -/
@[expose] noncomputable def totalNuclearCharge {M : ℕ} (z : Fin M → ℝ≥0) : ℝ :=
  ∑ k, (z k : ℝ)

theorem totalNuclearCharge_nonneg {M : ℕ} (z : Fin M → ℝ≥0) :
    0 ≤ totalNuclearCharge z := by
  unfold totalNuclearCharge
  positivity

/-- The explicit coefficient in the unit-radius near-core attraction bound. -/
@[expose] noncomputable def attractionKineticCoefficient {M : ℕ}
    (z : Fin M → ℝ≥0) : ℝ :=
  totalNuclearCharge z * (8 * Real.pi) ^ ((2 : ℝ) / 5)

theorem attractionKineticCoefficient_nonneg {M : ℕ} (z : Fin M → ℝ≥0) :
    0 ≤ attractionKineticCoefficient z := by
  unfold attractionKineticCoefficient
  exact mul_nonneg (totalNuclearCharge_nonneg z)
    (Real.rpow_nonneg (by positivity [Real.pi_pos.le]) _)

private theorem lintegral_tfDensity_rpow_eq (ρ : TFDensity) :
    (∫⁻ x : Position, ENNReal.ofReal (ρ.val x) ^ ((5 : ℝ) / 3) ∂volume) =
      ENNReal.ofReal (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) ∂volume) := by
  calc
    _ = ∫⁻ x : Position, ENNReal.ofReal ((ρ.val x) ^ ((5 : ℝ) / 3)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [tfDensity_ae_nonneg ρ] with x hx
      rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      (integrable_tfDensity_rpow_five_thirds ρ)
      (by filter_upwards [tfDensity_ae_nonneg ρ] with x hx; positivity)).symm

private theorem integral_inv_norm_mul_eq_coulombPotential_toReal
    (ρ : TFDensity) (x : Position) :
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

/-- Unit-radius one-centre attraction bound in real form. -/
theorem integral_inv_norm_mul_tfDensity_le (ρ : TFDensity) (x : Position) :
    (∫ y : Position, ‖y - x‖⁻¹ * ρ.val y) ≤
      (8 * Real.pi) ^ ((2 : ℝ) / 5) *
          (∫ y : Position, (ρ.val y) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        tfMass ρ := by
  have hp := coulombPotential_tfDensityMeasure_le ρ x 1 zero_lt_one
  rw [lintegral_tfDensity_rpow_eq] at hp
  have hrhs : (ENNReal.ofReal (8 * Real.pi * Real.sqrt 1)) ^ ((2 : ℝ) / 5) *
          ENNReal.ofReal (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        ENNReal.ofReal (1 / 1) * ENNReal.ofReal (tfMass ρ) ≠ ⊤ := by
      apply ENNReal.add_ne_top.2
      exact ⟨ENNReal.mul_ne_top (by finiteness) (by finiteness),
        ENNReal.mul_ne_top (by finiteness) (by finiteness)⟩
  have ht := (ENNReal.toReal_le_toReal
    (coulombPotential_tfDensityMeasure_lt_top ρ x).ne hrhs).2 hp
  rw [integral_inv_norm_mul_eq_coulombPotential_toReal] 
  have hparts := ENNReal.add_ne_top.mp hrhs
  rw [ENNReal.toReal_add hparts.1 hparts.2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at ht
  rw [ENNReal.toReal_ofReal (by positivity [Real.pi_pos.le]),
    ENNReal.toReal_ofReal (integral_tfDensity_rpow_five_thirds_nonneg ρ),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 1),
    ENNReal.toReal_ofReal (tfMass_nonneg ρ)] at ht
  simpa only [Real.sqrt_one, mul_one, one_div, inv_one, ENNReal.ofReal_one,
    ENNReal.toReal_ofReal, one_mul, Real.rpow_one] using ht

/-- Summed unit-radius nuclear attraction bound. -/
theorem integral_tfNuclearPotential_mul_le {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) :
    (∫ x : Position, tfNuclearPotential z R x * ρ.val x) ≤
      attractionKineticCoefficient z *
          (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        totalNuclearCharge z * tfMass ρ := by
  unfold tfNuclearPotential
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => by
    simpa only [div_eq_mul_inv, NNReal.smul_def, mul_assoc] using
      (integrable_inv_norm_mul_tfDensity ρ (R k)).const_mul (z k : ℝ))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun k _ =>
    mul_le_mul_of_nonneg_left (integral_inv_norm_mul_tfDensity_le ρ (R k)) (z k).property
  simp_rw [mul_add] at hsum
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  calc
    _ = ∑ k, (z k : ℝ) *
        (∫ y : Position, ‖y - R k‖⁻¹ * ρ.val y) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show (fun a : Position => (z k : ℝ) / ‖a - R k‖ * ρ.val a) =
          fun a => (z k : ℝ) * (‖a - R k‖⁻¹ * ρ.val a) by
        funext a
        rw [div_eq_mul_inv]
        ring]
      exact MeasureTheory.integral_const_mul _ _
    _ ≤ (∑ k, (z k : ℝ)) *
          ((8 * Real.pi) ^ ((2 : ℝ) / 5) *
            (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5)) +
        (∑ k, (z k : ℝ)) * tfMass ρ := hsum
    _ = _ := by
      rw [attractionKineticCoefficient, totalNuclearCharge]
      ring

/-- The explicit whole-carrier lower-bound constant at mass cap `ν`. -/
@[expose] noncomputable def tfCoercivityConstant {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) : ℝ :=
  youngCoercivityConstant a.val (attractionKineticCoefficient z) +
    totalNuclearCharge z * (ν : ℝ)

theorem tfCoercivityConstant_nonneg {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) :
    0 ≤ tfCoercivityConstant a ν z := by
  unfold tfCoercivityConstant
  exact add_nonneg
    (youngCoercivityConstant_nonneg a.property (attractionKineticCoefficient_nonneg z))
    (mul_nonneg (totalNuclearCharge_nonneg z) ν.property)

/-- Concrete Thomas--Fermi coercivity at a fixed mass cap. -/
theorem tfFunctional_coercive_lower_bound {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ)) :
    a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
        tfCoercivityConstant a ν z ≤ tfFunctional a z R ρ := by
  apply tfFunctional_lower_bound_of_attraction_le a z R ρ
    (attractionKineticCoefficient z) (totalNuclearCharge z * (ν : ℝ))
    (integral_tfDensity_rpow_five_thirds_nonneg ρ)
    (attractionKineticCoefficient_nonneg z)
    ?_ (tfCoulombEnergy_nonneg ρ ρ)
  calc
    _ ≤ attractionKineticCoefficient z *
          (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        totalNuclearCharge z * tfMass ρ := integral_tfNuclearPotential_mul_le z R ρ
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left hmass (totalNuclearCharge_nonneg z)) _

/-- The corresponding uniform lower bound after discarding the nonnegative
half-kinetic term. -/
theorem tfFunctional_lower_bound {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ)) :
    -tfCoercivityConstant a ν z ≤ tfFunctional a z R ρ := by
  calc
    -tfCoercivityConstant a ν z ≤
        a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
          tfCoercivityConstant a ν z := by
      have hkin : 0 ≤ a.val / 2 *
          (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) :=
        mul_nonneg (div_nonneg a.property.le (by norm_num))
          (integral_tfDensity_rpow_five_thirds_nonneg ρ)
      linarith only [hkin]
    _ ≤ _ := tfFunctional_coercive_lower_bound a ν z R ρ hmass

/-- Ordinary-library form of finiteness for both exact and relaxed TF
variational energies. -/
theorem tfEnergy_ne_top_ne_bot_library {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfEnergy a ν z R ≠ ⊤ ∧ tfEnergy a ν z R ≠ ⊥ ∧
      tfRelaxedEnergy a ν z R ≠ ⊤ ∧ tfRelaxedEnergy a ν z R ≠ ⊥ := by
  apply tfEnergies_ne_top_ne_bot_of_lower_bound a ν z R (tfCoercivityConstant a ν z)
  exact fun ρ hρ => tfFunctional_lower_bound a ν z R ρ hρ

end LiebThirring.TFFunctional

end
