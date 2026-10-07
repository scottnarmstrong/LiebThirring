/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.PotentialEstimates
import all LiebThirring.Electrostatics.Basic

/-! # Integrable pairings for the Thomas--Fermi first variation

Lieb–Simon (1977) II.10, pp. 40--43. The potential is finite at every
point for the actual TF carrier. Its integral against a second density is
exactly twice the half-Coulomb energy.
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

/-- The kinetic derivative belongs to the conjugate Lebesgue space. -/
theorem memLp_tfDensity_rpow_two_thirds (ρ : TFDensity) :
    MemLp (fun x : Position => (ρ.val x) ^ ((2 : ℝ) / 3))
      (ENNReal.ofReal ((5 : ℝ) / 2)) volume := by
  have h := (Lp.memLp ρ.val).norm_rpow_div ((2 : ℝ≥0∞) / 3)
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at h
  have he : ((5 : ℝ≥0∞) / 3) / ((2 : ℝ≥0∞) / 3) =
      ENNReal.ofReal ((5 : ℝ) / 2) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.div_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (by norm_num)) ENNReal.ofReal_ne_top).mp
    norm_num [ENNReal.toReal_div]
  rw [he] at h
  apply (memLp_congr_ae (show (fun x : Position => ‖ρ.val x‖ ^ ((2 : ℝ) / 3)) =ᵐ[volume]
      (fun x => (ρ.val x) ^ ((2 : ℝ) / 3)) from ?_)).mp h
  filter_upwards [tfDensity_ae_nonneg ρ] with x hx
  rw [Real.norm_of_nonneg hx]

theorem integrable_kinetic_pair (ρ σ : TFDensity) :
    Integrable (fun x : Position => (ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) volume := by
  let : ENNReal.HolderTriple (ENNReal.ofReal ((5 : ℝ) / 2))
      ((5 : ℝ≥0∞) / 3) 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr (by norm_num),
        ENNReal.inv_ne_top.mpr (by norm_num)⟩) (by norm_num)).mp
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr (by norm_num))
      (ENNReal.inv_ne_top.mpr (by norm_num))]
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div]⟩
  exact (memLp_tfDensity_rpow_two_thirds ρ).integrable_mul (Lp.memLp σ.val)

theorem measurable_tfDensity_potential (ρ : TFDensity) :
    Measurable (fun x : Position => (coulombPotential (tfDensityMeasure ρ) x).toReal) :=
  measurable_coulombKernel.lintegral_prod_right.ennreal_toReal

theorem integrable_potential_pair (ρ σ : TFDensity) :
    Integrable (fun x : Position =>
      (coulombPotential (tfDensityMeasure ρ) x).toReal * σ.val x) volume := by
  apply (integrable_tfDensity σ).bdd_mul
    (measurable_tfDensity_potential ρ).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (coulombPotential_tfDensityMeasure_le_norm ρ x 1 zero_lt_one)
  have hn : 0 ≤ (8 * Real.pi * Real.sqrt 1) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ + tfMass ρ / 1 :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))
      (div_nonneg (tfMass_nonneg ρ) zero_lt_one.le)
  exact (by simpa only [ENNReal.toReal_ofReal hn] using h)

/-- The factor two is essential: `tfCoulombEnergy` already includes one half. -/
theorem integral_potential_pair (ρ σ : TFDensity) :
    (∫ x : Position, (coulombPotential (tfDensityMeasure ρ) x).toReal * σ.val x) =
      2 * tfCoulombEnergy ρ σ := by
  have hi := integrable_potential_pair ρ σ
  have hn : ∀ᵐ x ∂(volume : Measure Position),
      0 ≤ (coulombPotential (tfDensityMeasure ρ) x).toReal * σ.val x := by
    filter_upwards [tfDensity_ae_nonneg σ] with x hx
    exact mul_nonneg ENNReal.toReal_nonneg hx
  have he : ENNReal.ofReal (∫ x : Position,
      (coulombPotential (tfDensityMeasure ρ) x).toReal * σ.val x) =
      coulombEnergy (tfDensityMeasure σ) (tfDensityMeasure ρ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi hn]
    change _ = ∫⁻ x : Position, coulombPotential (tfDensityMeasure ρ) x
      ∂(volume.withDensity (fun x => ENNReal.ofReal (σ.val x)))
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (coulombPotential (tfDensityMeasure ρ)) from
        measurable_coulombKernel.lintegral_prod_right)]
    apply lintegral_congr_ae
    filter_upwards [tfDensity_ae_nonneg σ] with x hx
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (coulombPotential_tfDensityMeasure_lt_top ρ x).ne,
      mul_comm, Pi.mul_apply]
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), coulombEnergy_symm] at h
  rw [h, tfCoulombEnergy]
  ring

end LiebThirring.TFMinimizer

end
