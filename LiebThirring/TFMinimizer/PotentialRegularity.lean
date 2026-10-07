/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.FirstVariationPairing
import all LiebThirring.Electrostatics.Basic
import all LiebThirring.Electrostatics.FaceMeasurePotential

/-! # Continuity and decay of TF electronic potentials

Lieb–Simon (1977) II.7 and II.17. The local Holder bound tends to zero
with the cap radius. Capped potentials of the actual finite density measure
are continuous and decay.
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem lintegral_coulombKernel_ball_tfDensity_le (ρ : TFDensity)
    (x : Position) (r : ℝ) (hr : 0 < r) :
    (∫⁻ y in ball x r, coulombKernel x y ∂tfDensityMeasure ρ) ≤
      ENNReal.ofReal ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖) := by
  change (∫⁻ y in ball x r, coulombKernel x y
    ∂volume.withDensity (fun y => ENNReal.ofReal (ρ.val y))) ≤ _
  rw [restrict_withDensity measurableSet_ball,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_coulombKernel_right x)]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (ball x r))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      ((5 : ℝ) / 2).HolderConjugate ((5 : ℝ) / 3))
    (measurable_coulombKernel_right x).aemeasurable
    (Lp.memLp ρ.val).aemeasurable.ennreal_ofReal.restrict
  rw [lintegral_coulombKernel_rpow_ball x r hr] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left
    (ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
      (by norm_num)) bot_le)
  norm_num only [one_div_div] at hb
  rw [lintegral_tfDensity_rpow_three_fifths_eq_norm] at hb
  have hC : 0 ≤ (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg (by positivity) _
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul hC] at hb
  convert hb using 1
  norm_num [Pi.mul_apply, mul_comm]

theorem coulombPotential_tfDensity_le_capped_add (ρ : TFDensity)
    (r : ℝ) (hr : 0 < r) (x : Position) :
    coulombPotential (tfDensityMeasure ρ) x ≤
      cappedCoulombPotential (tfDensityMeasure ρ) r x +
        ENNReal.ofReal ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖) := by
  have hk : ∀ y : Position, coulombKernel x y ≤ cappedCoulombKernel r x y +
      (ball x r).indicator (coulombKernel x) y := by
    intro y
    by_cases hy : y ∈ ball x r
    · rw [indicator_of_mem hy]
      exact le_add_left le_rfl
    · have hd : r ≤ ‖x - y‖ := by
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
      rw [indicator_of_notMem hy, add_zero]
      simp only [cappedCoulombKernel, max_eq_right hd, coulombKernel, le_refl]
  calc
    _ ≤ ∫⁻ y : Position, cappedCoulombKernel r x y +
        (ball x r).indicator (coulombKernel x) y ∂tfDensityMeasure ρ := lintegral_mono hk
    _ = cappedCoulombPotential (tfDensityMeasure ρ) r x +
        ∫⁻ y in ball x r, coulombKernel x y ∂tfDensityMeasure ρ := by
      rw [lintegral_add_left (measurable_cappedCoulombKernel_right r x),
        lintegral_indicator measurableSet_ball]
      rfl
    _ ≤ _ := add_le_add le_rfl (lintegral_coulombKernel_ball_tfDensity_le ρ x r hr)

theorem dist_tfDensity_potential_capped_le (ρ : TFDensity)
    (r : ℝ) (hr : 0 < r) (x : Position) :
    dist (coulombPotential (tfDensityMeasure ρ) x).toReal
      (cappedCoulombPotential (tfDensityMeasure ρ) r x).toReal ≤
        (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ := by
  have hp := coulombPotential_tfDensityMeasure_lt_top ρ x
  have hq := cappedCoulombPotential_lt_top (tfDensityMeasure ρ) r hr x
  have hlo := ENNReal.toReal_mono hp.ne (cappedCoulombPotential_le (tfDensityMeasure ρ) r x)
  have hu := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨hq, ENNReal.ofReal_lt_top⟩).ne
    (coulombPotential_tfDensity_le_capped_add ρ r hr x)
  have hn : 0 ≤ (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  rw [ENNReal.toReal_add hq.ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hn] at hu
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith only [hu]

theorem tendsto_tfLocalPotentialBound_zero (ρ : TFDensity) :
    Tendsto (fun r : ℝ => (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖)
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun r : ℝ =>
      (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖) :=
    ((continuous_const.mul Real.continuous_sqrt).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 5))).mul continuous_const
  have h := hc.tendsto (0 : ℝ)
  simpa only [Real.sqrt_zero, mul_zero, Real.zero_rpow (by norm_num : (2 : ℝ) / 5 ≠ 0),
    zero_mul] using h

theorem continuous_tfDensity_potential (ρ : TFDensity) :
    Continuous (fun x : Position => (coulombPotential (tfDensityMeasure ρ) x).toReal) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ < ε :=
    ((tendsto_tfLocalPotentialBound_zero ρ).eventually_lt_const hε).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hr, hsmall⟩ := (eventually_mem_nhdsWithin.and he).exists
  refine ⟨fun x => (cappedCoulombPotential (tfDensityMeasure ρ) r x).toReal,
    continuous_toReal_cappedCoulombPotential _ r hr, ?_⟩
  intro x
  exact hsub ((dist_tfDensity_potential_capped_le ρ r hr x).trans_lt hsmall)

/-- Every capped potential of a finite measure decays without any moment assumption. -/
theorem tendsto_cappedCoulombPotential_zero (η : Measure Position) [IsFiniteMeasure η]
    (r : ℝ) (hr : 0 < r) :
    Tendsto (cappedCoulombPotential η r) (Bornology.cobounded Position) (𝓝 0) := by
  let : (Bornology.cobounded Position).IsCountablyGenerated := by
    rw [← comap_norm_atTop]
    infer_instance
  have hlim : ∀ᵐ y ∂η, Tendsto (fun x : Position => cappedCoulombKernel r x y)
      (Bornology.cobounded Position) (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [] with y
    have hn : Tendsto (fun x : Position => ‖x - y‖) (Bornology.cobounded Position) atTop :=
      tendsto_norm_cobounded_atTop.comp (tendsto_sub_const_cobounded y)
    have hm : Tendsto (fun x : Position => max r ‖x - y‖)
        (Bornology.cobounded Position) atTop :=
      tendsto_atTop_mono (fun _ => le_max_right _ _) hn
    simpa only [cappedCoulombKernel, ENNReal.inv_top, Function.comp_def] using
      (ENNReal.tendsto_ofReal_atTop.comp hm).inv
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := η) (l := Bornology.cobounded Position)
    (F := fun x y : Position => cappedCoulombKernel r x y)
    (f := fun _ => (0 : ℝ≥0∞)) (fun _ => (ENNReal.ofReal r)⁻¹)
    (Eventually.of_forall (measurable_cappedCoulombKernel_right r))
    (Eventually.of_forall (fun x => Eventually.of_forall (cappedCoulombKernel_le_cap r x)))
    (by rw [lintegral_const]; exact (ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hr)) (measure_lt_top η univ)).ne) hlim
  change Tendsto (fun x : Position => ∫⁻ y, cappedCoulombKernel r x y ∂η)
    (Bornology.cobounded Position) (𝓝 0)
  simpa only [lintegral_zero] using h

theorem tendsto_tfDensity_potential_zero (ρ : TFDensity) :
    Tendsto (fun x : Position => (coulombPotential (tfDensityMeasure ρ) x).toReal)
      (Bornology.cobounded Position) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ < ε / 2 :=
    ((tendsto_tfLocalPotentialBound_zero ρ).eventually_lt_const (half_pos hε)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨r, hr, hsmall⟩ := (eventually_mem_nhdsWithin.and he).exists
  have hc : Tendsto (fun x : Position => (cappedCoulombPotential (tfDensityMeasure ρ) r x).toReal)
      (Bornology.cobounded Position) (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp
        (tendsto_cappedCoulombPotential_zero (tfDensityMeasure ρ) r hr)
  filter_upwards [(Metric.tendsto_nhds.mp hc) (ε / 2) (half_pos hε)] with x hx
  exact (dist_triangle _ (cappedCoulombPotential (tfDensityMeasure ρ) r x).toReal 0).trans_lt
    (by linarith only [dist_tfDensity_potential_capped_le ρ r hr x, hx, hsmall])

end LiebThirring.TFMinimizer

end
