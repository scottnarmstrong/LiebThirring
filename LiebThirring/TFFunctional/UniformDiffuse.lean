/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Diffuse
public import LiebThirring.TFFunctional.PotentialNorm

/-! # Uniformly small potentials of diffuse fixed-mass densities

The near/far estimate first fixes a large cutoff radius, then lets the cloud's
Lp norm vanish. No L1 convergence of a fixed positive mass is claimed.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem eventually_coulombPotential_tfDiffuseDensity_le (ν : ℝ≥0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in atTop, ∀ x : Position,
      coulombPotential (tfDensityMeasure (tfDiffuseDensity ν j)) x ≤ ENNReal.ofReal η := by
  let r : ℝ := 1 + 2 * (ν : ℝ) / η
  have hr : 0 < r := by dsimp [r]; positivity
  have hfar : (ν : ℝ) / r ≤ η / 2 := by
    apply (div_le_iff₀ hr).mpr
    dsimp [r]
    have hcancel : η * (2 * (ν : ℝ) / η) = 2 * (ν : ℝ) := by
      field_simp
    nlinarith
  let C : ℝ := (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5)
  have hnear : Tendsto (fun j => C * ‖(tfDiffuseDensity ν j).val‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_norm_tfDiffuseDensity ν).const_mul C
  filter_upwards [hnear.eventually_lt_const (half_pos hη)] with j hj x
  apply (coulombPotential_tfDensityMeasure_le_norm (tfDiffuseDensity ν j) x r hr).trans
  apply ENNReal.ofReal_le_ofReal
  rw [tfMass_tfDiffuseDensity]
  change C * ‖(tfDiffuseDensity ν j).val‖ + (ν : ℝ) / r ≤ η
  linarith

end LiebThirring.TFFunctional

end
