/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeightedDensity
public import LiebThirring.Sobolev.SchwartzCutoff
import LiebThirring.Theorems.KineticEnergySchwartz

/-!
# Fourier graph norm and compact cutoffs

The radial Fourier L² weight is exactly the kinetic form divided by `(2π)²`.
Schwartz cutoff convergence therefore passes from spatial first derivatives to
this Fourier graph seminorm without using the weak derivative bridge.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap FourierTransform ContDiff Topology

namespace LiebThirring.Sobolev

/-- The radial Fourier graph measure on the configuration carrier. -/
@[expose] noncomputable def radialFourierMeasure (N : ℕ) : Measure (Configuration N) :=
  volume.withDensity (fun ξ => ENNReal.ofReal (‖ξ‖ ^ 2))

/-- The radial Fourier seminorm squared is the Fourier kinetic form up to `(2π)²`. -/
theorem kineticEnergy_eq_radialFourier_eLpNorm {N q : ℕ} (u : State N q) :
    kineticEnergy u = ENNReal.ofReal ((2 * Real.pi) ^ 2) *
      eLpNorm (fun ξ => (𝓕 u : State N q) ξ) 2 (radialFourierMeasure N) ^ 2 := by
  let v : State N q := 𝓕 u
  have hm : Measurable (fun ξ : Configuration N => ENNReal.ofReal (‖ξ‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (continuous_norm.pow 2).measurable
  have ha : AEStronglyMeasurable (fun ξ => v ξ) (radialFourierMeasure N) :=
    (Lp.aestronglyMeasurable v).mono_ac (withDensity_absolutelyContinuous _ _)
  have hs : eLpNorm (fun ξ => v ξ) 2 (radialFourierMeasure N) ^ 2 =
      ∫⁻ ξ, (‖v ξ‖₊ : ℝ≥0∞) ^ 2 ∂radialFourierMeasure N := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat, enorm_eq_nnnorm] using
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) ha
  rw [show (fun ξ => (𝓕 u : State N q) ξ) = (fun ξ => v ξ) from rfl, hs]
  change (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
    (‖v ξ‖₊ : ℝ≥0∞) ^ 2) = _
  rw [radialFourierMeasure, lintegral_withDensity_eq_lintegral_mul₀ hm.aemeasurable
    ((Lp.aestronglyMeasurable v).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ξ
  dsimp only [Pi.mul_apply]
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, mul_assoc]
  rfl

/-- The Fourier radial seminorm is the square root of the kinetic form divided by `(2π)²`. -/
theorem radialFourier_eLpNorm_eq {N q : ℕ} (u : State N q) :
    eLpNorm (fun ξ => (𝓕 u : State N q) ξ) 2 (radialFourierMeasure N) =
      ((ENNReal.ofReal ((2 * Real.pi) ^ 2))⁻¹ * kineticEnergy u) ^ (2 : ℝ)⁻¹ := by
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))).ne'
  rw [kineticEnergy_eq_radialFourier_eLpNorm, ← mul_assoc,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_mul]
  simpa only [Nat.cast_ofNat] using (ENNReal.pow_rpow_inv_natCast
    (by decide : (2 : ℕ) ≠ 0)
    (eLpNorm (fun ξ => (𝓕 u : State N q) ξ) 2 (radialFourierMeasure N))).symm

/-- Spatial coordinate derivative convergence of Schwartz states implies kinetic convergence. -/
theorem tendsto_kineticEnergy_schwartz_of_directional {N q : ℕ}
    (φ : ℕ → 𝓢(Configuration N, SpinAmplitudes N q))
    (hφ : ∀ a : Fin N × Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (φ n) x (PiLp.single 2 a (1 : ℝ))) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => kineticEnergy ((φ n).toLp 2 volume)) atTop (𝓝 0) := by
  have hs (n : ℕ) (i : Fin N) (a : Fin 3) :
      (∫⁻ x, (‖fderiv ℝ (φ n) x (PiLp.single 2 (i, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) =
      eLpNorm (fun x => fderiv ℝ (φ n) x (PiLp.single 2 (i, a) (1 : ℝ))) 2 volume ^ 2 := by
    symm
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat, enorm_eq_nnnorm,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        ((((φ n).smooth ⊤).continuous_fderiv (by simp)).clm_apply
          (continuous_const (y := (PiLp.single 2 (i, a) (1 : ℝ) : Configuration N)))).aestronglyMeasurable
  have ht (i : Fin N) (a : Fin 3) : Tendsto (fun n =>
      eLpNorm (fun x => fderiv ℝ (φ n) x (PiLp.single 2 (i, a) (1 : ℝ))) 2 volume ^ 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp (hφ (i, a))
  have hi (i : Fin N) := tendsto_finsetSum Finset.univ (fun a _ => ht i a)
  have hall := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [kineticEnergy_schwartz, hs, Finset.sum_const_zero] using hall

/-- Kinetic convergence implies convergence of the radial Fourier graph seminorm. -/
theorem tendsto_radialFourier_eLpNorm_of_kinetic {N q : ℕ} (u : ℕ → State N q)
    (hu : Tendsto (fun n => kineticEnergy (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ξ => (𝓕 (u n) : State N q) ξ)
      2 (radialFourierMeasure N)) atTop (𝓝 0) := by
  have hc : (ENNReal.ofReal ((2 * Real.pi) ^ 2))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))).ne'
  have hm := ENNReal.Tendsto.const_mul hu (Or.inr hc)
  have hr := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).continuousAt.tendsto.comp hm
  simpa only [Function.comp_def, mul_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
    ← radialFourier_eLpNorm_eq] using hr

end LiebThirring.Sobolev

end
