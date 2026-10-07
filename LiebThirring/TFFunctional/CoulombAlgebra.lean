/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Electrostatics.CoulombPositivity

/-! # Positive-measure Coulomb algebra

Additivity and scalar transport of the actual extended Coulomb energy, without
an assumed finite value. Proof: the TF finiteness estimates, mass completion and TF scaling.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

theorem coulombEnergy_add_left (μ ν σ : Measure Position) :
    coulombEnergy (μ + ν) σ = coulombEnergy μ σ + coulombEnergy ν σ := by
  simp only [coulombEnergy_eq_lintegral]
  exact lintegral_add_measure _ _ _

theorem coulombEnergy_add_right (μ ν σ : Measure Position)
    [SFinite ν] [SFinite σ] :
    coulombEnergy μ (ν + σ) = coulombEnergy μ ν + coulombEnergy μ σ := by
  simp only [coulombEnergy_eq_lintegral]
  simp_rw [lintegral_add_measure]
  exact lintegral_add_left measurable_coulombKernel.lintegral_prod_right _

theorem coulombEnergy_smul_left (b : ℝ≥0∞) (μ ν : Measure Position) :
    coulombEnergy (b • μ) ν = b * coulombEnergy μ ν := by
  simp only [coulombEnergy_eq_lintegral]
  exact lintegral_smul_measure b _

theorem coulombEnergy_smul_right (b : ℝ≥0∞) (μ ν : Measure Position) [SFinite ν] :
    coulombEnergy μ (b • ν) = b * coulombEnergy μ ν := by
  simp only [coulombEnergy_eq_lintegral]
  simp_rw [lintegral_smul_measure]
  exact lintegral_const_mul _ measurable_coulombKernel.lintegral_prod_right

/-- Under spatial contraction by β⁻¹ the Coulomb kernel acquires a factor β. -/
theorem coulombKernel_inv_smul (β : ℝ) (hβ : 0 < β) (x y : Position) :
    coulombKernel (β⁻¹ • x) (β⁻¹ • y) = ENNReal.ofReal β * coulombKernel x y := by
  unfold coulombKernel
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ),
    ENNReal.ofReal_mul (inv_nonneg.mpr hβ.le), ENNReal.mul_inv]
  · rw [ENNReal.ofReal_inv_of_pos hβ, inv_inv]
  · exact Or.inr ENNReal.ofReal_ne_top
  · exact Or.inl ENNReal.ofReal_ne_top

/-- Exact Coulomb scaling for the actual pushed-forward measures. -/
theorem coulombEnergy_map_smul (β : ℝ) (hβ : 0 < β) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    coulombEnergy (μ.map (fun x => β⁻¹ • x)) (ν.map (fun x => β⁻¹ • x)) =
      ENNReal.ofReal β * coulombEnergy μ ν := by
  have hm : Measurable (fun x : Position => β⁻¹ • x) :=
    (continuous_id.const_smul β⁻¹).measurable
  simp only [coulombEnergy_eq_lintegral]
  calc
    _ = ∫⁻ x, ∫⁻ y, coulombKernel (β⁻¹ • x) (β⁻¹ • y) ∂ν ∂μ := by
      rw [lintegral_map measurable_coulombKernel.lintegral_prod_right hm]
      apply lintegral_congr_ae
      filter_upwards [] with x
      exact lintegral_map measurable_coulombKernel.of_uncurry_left hm
    _ = _ := by
      simp_rw [coulombKernel_inv_smul β hβ,
        lintegral_const_mul _ measurable_coulombKernel.of_uncurry_left,
        lintegral_const_mul _ measurable_coulombKernel.lintegral_prod_right]

end LiebThirring.TFFunctional

end
