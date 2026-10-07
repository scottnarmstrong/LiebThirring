/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.RellichKernel
public import LiebThirring.Variational.RellichTail

/-! # Local Rellich compactness on the Fourier form graph -/

public section

open MeasureTheory Filter WithLp
open scoped Topology FourierTransform ENNReal

namespace LiebThirring

/-- The low-frequency state has the continuous inverse-integral representative. -/
theorem lowFrequencyState_coeFn {N q : ℕ} (R : ℝ) (u : State N q) :
    ⇑(lowFrequencyState R u) =ᵐ[volume]
      inverseCutoffIntegral (Metric.closedBall 0 R) u := by
  apply Fourier.fourierInv_toLp_ae_eq
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (state_integrableOn (𝓕 u) (Metric.closedBall 0 R) (isCompact_closedBall 0 R).measure_ne_top)

/-- Finite-frequency states converge strongly after restriction to any finite-measure set. -/
theorem tendsto_stateIndicator_lowFrequencyState {N q : ℕ}
    (R : ℝ) (b : Set (Configuration N)) (hb : MeasurableSet b) (hμb : volume b ≠ ⊤)
    {u : ℕ → State N q} {v : State N q}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    Tendsto (fun n => stateIndicatorCLM b hb (lowFrequencyState R (u n))) atTop
      (𝓝 (stateIndicatorCLM b hb (lowFrequencyState R v))) := by
  have h := tendsto_integral_inverseCutoffIntegral_sub_sq (Metric.closedBall 0 R) b
    measurableSet_closedBall (isCompact_closedBall 0 R).measure_ne_top hμb hu K hK
  have he (n : ℕ) : ‖stateIndicatorCLM b hb
      (lowFrequencyState R (u n) - lowFrequencyState R v)‖ ^ 2 =
      ∫ x in b, ‖inverseCutoffIntegral (Metric.closedBall 0 R) (u n) x -
        inverseCutoffIntegral (Metric.closedBall 0 R) v x‖ ^ 2 := by
    rw [norm_stateIndicatorCLM_sq]
    apply integral_congr_ae
    filter_upwards [((Lp.coeFn_sub (lowFrequencyState R (u n)) (lowFrequencyState R v)).and
      ((lowFrequencyState_coeFn R (u n)).and (lowFrequencyState_coeFn R v))).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hx
    simp only [Pi.sub_apply] at hx
    rw [hx.1, hx.2.1, hx.2.2]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := (Real.continuous_sqrt.tendsto 0).comp h
  simpa only [Function.comp_def, ← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, map_sub] using ht

/-- Weak graph convergence and a graph-norm bound imply strong local L² convergence.
This is the local Rellich bridge; no local compactness assumption is an input. -/
theorem tendsto_stateIndicator_of_formGraph_weak {N q : ℕ}
    (b : Set (Configuration N)) (hb : MeasurableSet b) (hμb : volume b ≠ ⊤)
    {u : ℕ → Sobolev.formGraph N q} {v : Sobolev.formGraph N q}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) :
    Tendsto (fun n => stateIndicatorCLM b hb ((u n : Sobolev.FormGraphAmbient N q) none))
      atTop (𝓝 (stateIndicatorCLM b hb ((v : Sobolev.FormGraphAmbient N q) none))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨R, hR, hlarge⟩ := exists_pos_lt_mul (mul_pos hp (show 0 < ε / 3 by positivity))
    (max K ‖v‖)
  have hden : 0 < 2 * Real.pi * R := mul_pos hp hR
  have htail (w : Sobolev.formGraph N q) (hw : ‖w‖ ≤ max K ‖v‖) :
      dist (stateIndicatorCLM b hb ((w : Sobolev.FormGraphAmbient N q) none))
        (stateIndicatorCLM b hb (lowFrequencyState R ((w : Sobolev.FormGraphAmbient N q) none)))
        < ε / 3 := by
    rw [dist_eq_norm, ← map_sub]
    apply lt_of_le_of_lt (norm_stateIndicatorCLM_le b hb _)
      (lt_of_le_of_lt (norm_sub_lowFrequencyState_le_of_formGraph R hR w) ?_)
    apply (div_lt_iff₀ hden).mpr
    calc
      ‖w‖ ≤ max K ‖v‖ := hw
      _ < R * (2 * Real.pi * (ε / 3)) := hlarge
      _ = ε / 3 * (2 * Real.pi * R) := by ring
  have hstate (n : ℕ) : ‖(u n : Sobolev.FormGraphAmbient N q) none‖ ≤ K :=
    (PiLp.norm_apply_le (u n : Sobolev.FormGraphAmbient N q) none).trans (hK n)
  have hweak := tendsto_inner_formGraph_coordinate hu none
  have hlow := tendsto_stateIndicator_lowFrequencyState R b hb hμb hweak K hstate
  filter_upwards [(Metric.tendsto_nhds.mp hlow) (ε / 3) (by positivity)] with n hn
  calc
    _ ≤ dist (stateIndicatorCLM b hb ((u n : Sobolev.FormGraphAmbient N q) none))
        (stateIndicatorCLM b hb (lowFrequencyState R ((u n : Sobolev.FormGraphAmbient N q) none))) +
        dist (stateIndicatorCLM b hb (lowFrequencyState R ((u n : Sobolev.FormGraphAmbient N q) none)))
        (stateIndicatorCLM b hb ((v : Sobolev.FormGraphAmbient N q) none)) := dist_triangle _ _ _
    _ ≤ _ + (dist (stateIndicatorCLM b hb (lowFrequencyState R ((u n : Sobolev.FormGraphAmbient N q) none)))
        (stateIndicatorCLM b hb (lowFrequencyState R ((v : Sobolev.FormGraphAmbient N q) none))) +
        dist (stateIndicatorCLM b hb (lowFrequencyState R ((v : Sobolev.FormGraphAmbient N q) none)))
        (stateIndicatorCLM b hb ((v : Sobolev.FormGraphAmbient N q) none))) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add
      (htail (u n) ((hK n).trans (le_max_left _ _)))
      (add_lt_add hn (by simpa only [dist_comm] using htail v (le_max_right _ _)))
    _ = ε := by ring

end LiebThirring
end
