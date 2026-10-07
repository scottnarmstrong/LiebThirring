/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.KineticEnergy
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Smooth approximation in the Fourier graph weight

The weighted approximation prerequisite of the weak-derivative characterization, in every finite dimension.
Both errors are errors of the difference, rather than differences of quadratic energies.
This module does not assert the weak-derivative characterization or the spatial
compact smooth graph core.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap ContDiff FourierTransform

namespace LiebThirring.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Squared radius times volume is finite on compact sets in every finite dimension. -/
theorem isFiniteMeasureOnCompacts_norm_sq :
    IsFiniteMeasureOnCompacts ((volume : Measure E).withDensity
      (fun x => ENNReal.ofReal (‖x‖ ^ 2))) := by
  constructor
  intro K hK
  rw [withDensity_apply _ hK.measurableSet]
  have hi := (continuous_norm.pow 2).continuousOn.integrableOn_compact
    (μ := (volume : Measure E)) hK
  change IntegrableOn (fun x : E => ‖x‖ ^ 2) K volume at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖x‖))]
  exact ENNReal.ofReal_lt_top

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F] in
/-- Finite squared-norm integral is the L² membership criterion. -/
theorem memLp_two_of_lintegral_norm_sq {μ : Measure E} {f : E → F}
    (hf : AEStronglyMeasurable f μ) (h : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    MemLp f 2 μ := by
  have he : eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat, enorm_eq_nnnorm] using
      (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf)
  rw [← he] at h
  exact (ENNReal.pow_lt_top_iff.mp h).resolve_right (by decide)

/-- Compact smooth Fourier-side approximants control the unweighted and radial weighted errors. -/
theorem exists_compact_smooth_weighted_approximation (u : Lp F 2 (volume : Measure E))
    (hu : (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖u x‖₊ : ℝ≥0∞) ^ 2) < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (fun x => u x - g x) 2 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (fun x => u x - g x) 2
        ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (‖x‖ ^ 2))) ≤
          ENNReal.ofReal ε := by
  let ν := (volume : Measure E).withDensity (fun x => ENNReal.ofReal (‖x‖ ^ 2))
  let μ := (volume : Measure E) + ν
  let : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_norm_sq
  let : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    change volume K + ν K < ⊤
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  have hm : Measurable (fun x : E => ENNReal.ofReal (‖x‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (continuous_norm.pow 2).measurable
  have haν : AEStronglyMeasurable (fun x => u x) ν :=
    (Lp.aestronglyMeasurable u).mono_ac (withDensity_absolutelyContinuous _ _)
  have haμ : AEStronglyMeasurable (fun x => u x) μ :=
    (Lp.aestronglyMeasurable u).add_measure haν
  have he : (∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂ν) =
      ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hm.aemeasurable
      ((Lp.aestronglyMeasurable u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)]
    apply lintegral_congr
    intro x
    dsimp only [Pi.mul_apply]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  have huμ : MemLp (fun x => u x) 2 μ := by
    apply memLp_two_of_lintegral_norm_sq haμ
    rw [lintegral_add_measure, he]
    apply ENNReal.add_lt_top.mpr
    refine ⟨?_, hu⟩
    have he₂ := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) (Lp.aestronglyMeasurable u)
    rw [← show eLpNorm (fun x => u x) 2 volume ^ 2 =
      ∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ 2 from by
        simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat, enorm_eq_nnnorm] using he₂]
    exact ENNReal.pow_lt_top (Lp.memLp u).eLpNorm_lt_top
  obtain ⟨g, hgK, hgC, hg⟩ := huμ.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hε
  refine ⟨g, hgK, hgC, ?_, ?_⟩
  · exact (eLpNorm_mono_measure (fun x => u x - g x) (show (volume : Measure E) ≤ μ from
      Measure.le_add_right le_rfl)).trans hg
  · exact (eLpNorm_mono_measure (fun x => u x - g x) (show ν ≤ μ from
      Measure.le_add_left le_rfl)).trans hg

/-- The kinetic-energy finiteness hypothesis gives the radial Fourier L² weight. -/
theorem fourier_radial_energy_lt_top {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) :
    (∫⁻ ξ : Configuration N, (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u) ξ‖₊ : ℝ≥0∞) ^ 2) <
        ⊤ := by
  have hm : Measurable (fun ξ : Configuration N => (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u) ξ‖₊ : ℝ≥0∞) ^ 2) :=
    (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2).mul
      ((Lp.stronglyMeasurable _).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
  unfold kineticEnergy at hu
  simp only [mul_assoc] at hu
  rw [lintegral_const_mul _ hm] at hu
  exact ENNReal.lt_top_of_mul_ne_top_right hu.ne hc

/-- Schwartz states approximate every finite-energy state in both Fourier graph weights. -/
theorem exists_schwartz_fourier_weighted_approximation {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(Configuration N, SpinAmplitudes N q),
      eLpNorm (fun ξ =>
        (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u) ξ - (𝓕 f) ξ)
          2 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (fun ξ =>
        (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u) ξ - (𝓕 f) ξ)
          2 ((volume : Measure (Configuration N)).withDensity
            (fun ξ => ENNReal.ofReal (‖ξ‖ ^ 2))) ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgK, hgC, hg₀, hg₁⟩ := exists_compact_smooth_weighted_approximation
    (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u)
    (fourier_radial_energy_lt_top u hu) hε
  refine ⟨𝓕⁻ (hgK.toSchwartzMap hgC), ?_⟩
  simpa only [FourierTransform.fourier_fourierInv_eq, HasCompactSupport.toSchwartzMap_toFun]
    using And.intro hg₀ hg₁

end LiebThirring.Sobolev

end
