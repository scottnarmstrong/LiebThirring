/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalReflection
import Mathlib.Tactic

/-!
# Bounded dominated convergence in physical complex L²

A finite-measure helper for the interval cutoff argument in the cube spectral theory.
It controls the physical L² norm of the difference of the functions. Applying
it separately to functions and their actual derivatives gives graph convergence.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace LiebThirring.TFCubes

/-- Uniformly bounded, almost-everywhere convergent functions converge in physical L²
on a finite measure space. -/
theorem tendsto_complexL2_of_bounded_ae_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → ℂ} {g : α → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (B : ℝ) (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ B)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n x ↦ ‖f n x - g x‖ ^ 2) (f := fun _ ↦ (0 : ℝ))
      (fun _ : α ↦ (2 * B) ^ 2)
      (fun n ↦ by
        exact (continuous_pow 2).comp_aestronglyMeasurable
          ((hf n).aestronglyMeasurable.fun_sub hg.aestronglyMeasurable).norm)
      (integrable_const ((2 * B) ^ 2))
      (fun n ↦ by
        filter_upwards [hfb n, hgb] with x hx hy
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (add_le_add hx hy) |>.trans_eq (two_mul B).symm) 2)
      (by
        filter_upwards [hlim] with x hx
        have h := (hx.sub_const (g x)).norm.pow 2
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h)
    simpa only [integral_zero] using h
  have hn : Tendsto
      (fun n ↦ ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    convert hsq using 1
    ext n
    rw [norm_complexL2_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with x hs hx hy
    simp only [Pi.sub_apply] at hs
    rw [hs, hx, hy]
  have hn' := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have hnorm : Tendsto
      (fun n ↦ ‖(hf n).toLp (f n) - hg.toLp g‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn'
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hnorm)

end LiebThirring.TFCubes

end
