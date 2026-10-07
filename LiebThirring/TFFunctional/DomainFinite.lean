/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFFunctional.CoulombBounds
public import LiebThirring.ThomasFermi.Functional
import all LiebThirring.Electrostatics.Basic

/-! # Finiteness of the Thomas--Fermi functional terms -/

public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace LiebThirring.TFFunctional

theorem integrable_inv_norm_mul_tfDensity (ρ : TFDensity) (x : Position) :
    Integrable (fun y : Position => ‖y - x‖⁻¹ * ρ.val y) volume := by
  have hm : AEStronglyMeasurable (fun y : Position => ‖y-x‖⁻¹ * ρ.val y) volume :=
    (((continuous_id.sub continuous_const).norm.measurable.inv).aestronglyMeasurable).mul
      (Lp.memLp ρ.val).aestronglyMeasurable
  refine ⟨hm, (hasFiniteIntegral_iff_ofReal ?_).2 ?_⟩
  · filter_upwards [tfDensity_ae_nonneg ρ] with y hy
    positivity
  · have heq : ∀ᵐ y ∂volume,
        ENNReal.ofReal (‖y-x‖⁻¹ * ρ.val y) =
          coulombKernel x y * ENNReal.ofReal (ρ.val y) := by
      filter_upwards [(volume : Measure Position).ae_ne x, tfDensity_ae_nonneg ρ] with y hne hy
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)),
        ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)), coulombKernel,
        norm_sub_rev]
    rw [lintegral_congr_ae heq]
    have hp := coulombPotential_tfDensityMeasure_lt_top ρ x
    rw [LiebThirring.coulombPotential, tfDensityMeasure,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
        (measurable_coulombKernel_right x)] at hp
    simpa only [Pi.mul_apply, mul_comm] using hp

theorem integrable_tfNuclearPotential_mul {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) :
    Integrable (fun x : Position => tfNuclearPotential z R x * ρ.val x) volume := by
  unfold tfNuclearPotential
  simp_rw [Finset.sum_mul]
  apply integrable_finsetSum
  intro k _
  simpa only [div_eq_mul_inv, NNReal.smul_def, mul_assoc] using
    (integrable_inv_norm_mul_tfDensity ρ (R k)).const_mul (z k : ℝ)

theorem tfCoulombEnergy_nonneg (ρ σ : TFDensity) : 0 ≤ tfCoulombEnergy ρ σ := by
  unfold tfCoulombEnergy
  positivity

theorem tfDensity_integrals_finite_library {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) < ⊤ ∧
      Integrable (fun x : Position => tfNuclearPotential z R x * ρ.val x) volume ∧
      Integrable (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3)) volume := by
  exact ⟨coulombEnergy_tfDensity_lt_top ρ σ,
    integrable_tfNuclearPotential_mul z R ρ, integrable_tfDensity_rpow_five_thirds ρ⟩

end LiebThirring.TFFunctional
end
