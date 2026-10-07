/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Screening.Radialization
import LiebThirring.Electrostatics.Gaussian
import all LiebThirring.Electrostatics.Basic
/-! # Exterior shell-mixture potentials and Coulomb integrability

Newton exterior formula and uniform separation bounds for finite measures.
-/

public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace LiebThirring

theorem coulombPotential_radialize_exterior (c y : Position) (μ : Measure Position)
    {r : ℝ} (hs : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hy : r < ‖y-c‖) :
    coulombPotential (radialize c μ) y = coulombKernel y c * μ univ := by
  rw [coulombPotential_radialize]
  calc
    _ = ∫⁻ _x, coulombKernel y c ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hs] with x hx
      rw [max_eq_left (hx.trans hy.le)]
      rfl
    _ = _ := lintegral_const _

theorem inverse_norm_eq_coulombKernel_toReal (y x : Position) :
    ‖y-x‖⁻¹ = (coulombKernel y x).toReal := by
  rw [coulombKernel, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem integral_inverse_norm_eq_potential (μ : Measure Position) (y : Position)
    (hf : coulombPotential μ y < ⊤) :
    (∫ x, ‖y-x‖⁻¹ ∂μ) = (coulombPotential μ y).toReal := by
  simp_rw [inverse_norm_eq_coulombKernel_toReal]
  exact integral_toReal measurable_coulombKernel.of_uncurry_left.aemeasurable
    (ae_lt_top measurable_coulombKernel.of_uncurry_left hf.ne)

theorem integrable_inverse_norm_of_potential_lt_top (μ : Measure Position) (y : Position)
    (hf : coulombPotential μ y < ⊤) : Integrable (fun x => ‖y-x‖⁻¹) μ := by
  simp_rw [inverse_norm_eq_coulombKernel_toReal]
  exact integrable_toReal_of_lintegral_ne_top
    measurable_coulombKernel.of_uncurry_left.aemeasurable hf.ne

/-- Separation from a closed ball bounds every point-pair distance. -/
theorem ae_distance_le_of_ball_separation (c y : Position) (μ : Measure Position)
    {r ε : ℝ} (hs : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hy : r + ε ≤ ‖y-c‖) :
    ∀ᵐ x ∂μ, ε ≤ ‖y-x‖ := by
  filter_upwards [hs] with x hx
  have ht : ‖y-c‖ ≤ ‖y-x‖ + ‖x-c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (y-x) (x-c)
  linarith only [hy, ht, hx]

theorem integral_inverse_norm_radialize_exterior (c y : Position)
    (μ : Measure Position) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hy : r < ‖y-c‖) :
    (∫ x, ‖y-x‖⁻¹ ∂radialize c μ) = (μ univ).toReal / ‖y-c‖ := by
  have hR : 0 < ‖y-c‖ := hr.trans_lt hy
  have hf : coulombPotential (radialize c μ) y < ⊤ := by
    rw [coulombPotential_radialize_exterior c y μ hs hy]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hR))
      (measure_lt_top μ univ)
  rw [integral_inverse_norm_eq_potential _ y hf,
    coulombPotential_radialize_exterior c y μ hs hy, ENNReal.toReal_mul,
    coulombKernel, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _), div_eq_mul_inv,
    mul_comm]

end LiebThirring
end
