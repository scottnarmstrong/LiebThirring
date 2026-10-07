/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity

/-! # Scaling errors in the regular-potential lower bound

This module records the elementary large-parameter limit for the exact error
appearing in the regular-potential lower bound.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LiebThirring.TFCoulomb

/-- The exact error in the regular-potential lower bound regular-potential lower bound. -/
noncomputable def scalingError (t Cq ℓ ν α : ℝ) : ℝ :=
  t * Cq * ℓ⁻¹ ^ 2 * α ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) +
    ν / (2 * Real.sqrt 3 * α * ℓ)

/-- For fixed parameters and positive cube length, the regular-potential lower bound scaling error tends
to zero as the scaling parameter tends to infinity. -/
theorem scalingError_tendsto_zero (t Cq ν : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (scalingError t Cq ℓ ν) atTop (𝓝 0) := by
  have hrpow : Tendsto (fun α : ℝ => α ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    simpa only [neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have hinv : Tendsto (fun α : ℝ => α⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hfirst :=
    (hrpow.const_mul (t * Cq * ℓ⁻¹ ^ 2)).mul_const (ν ^ ((4 : ℝ) / 3))
  have hsecond := hinv.const_mul (ν / (2 * Real.sqrt 3 * ℓ))
  have hsum := hfirst.add hsecond
  simp only [zero_mul, mul_zero, zero_add] at hsum
  convert hsum using 1
  ext α
  rw [scalingError, div_eq_mul_inv]
  field_simp [hℓ.ne', Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]

/-- Eventually, the absolute value of the regular-potential lower bound scaling error is below any
positive tolerance. -/
theorem eventually_abs_scalingError_lt (t Cq ν : ℝ) {ℓ ε : ℝ}
    (hℓ : 0 < ℓ) (hε : 0 < ε) :
    ∀ᶠ α : ℝ in atTop, |scalingError t Cq ℓ ν α| < ε := by
  simpa only [Set.mem_Ioo, abs_lt] using
    (scalingError_tendsto_zero t Cq ν hℓ).eventually
      (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)

end LiebThirring.TFCoulomb

end
