/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.TrialDensities

/-! # Diffuse TF densities with prescribed mass

Uniform ball densities have fixed mass and vanishing L^{5/3} norm as their
radii tend to infinity. They supply the inexpensive missing mass in mass completion.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem norm_tfBallDensity_rpow (ν : ℝ≥0) (c : Position)
    (r : {r : ℝ // 0 < r}) :
    ‖(tfBallDensity ν c r).val‖ =
      (ν : ℝ) * ballVolumeConstant ^ (-(2 : ℝ) / 5) * r.val ^ (-(6 : ℝ) / 5) := by
  rw [norm_tfBallDensity, div_eq_mul_inv, mul_assoc,
    ← Real.rpow_neg_one (ballVolumeConstant * r.val ^ 3),
    ← Real.rpow_add (mul_pos ballVolumeConstant_pos (pow_pos r.property 3))]
  norm_num only [show (-1 : ℝ) + 3 / 5 = -(2 : ℝ) / 5 by norm_num]
  rw [Real.mul_rpow ballVolumeConstant_pos.le (pow_nonneg r.property.le 3),
    ← Real.rpow_natCast, ← Real.rpow_mul r.property.le]
  norm_num only [show (3 : ℝ) * (-(2 : ℝ) / 5) = -(6 : ℝ) / 5 by norm_num]
  ring

/-- A sequence of increasingly diffuse ball densities of the same mass. -/
@[expose] noncomputable def tfDiffuseDensity (ν : ℝ≥0) (j : ℕ) : TFDensity :=
  tfBallDensity ν 0 ⟨(j : ℝ) + 1, by positivity⟩

theorem tfMass_tfDiffuseDensity (ν : ℝ≥0) (j : ℕ) :
    tfMass (tfDiffuseDensity ν j) = ν := tfMass_tfBallDensity _ _ _

theorem tendsto_norm_tfDiffuseDensity (ν : ℝ≥0) :
    Tendsto (fun j => ‖(tfDiffuseDensity ν j).val‖) atTop (𝓝 (0 : ℝ)) := by
  have hR : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun j : ℕ => ((j : ℝ) + 1) ^ (-(6 : ℝ) / 5)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 6 / 5)).comp hR using 1
    simp only [Function.comp_def, neg_div]
  simpa only [tfDiffuseDensity, norm_tfBallDensity_rpow, mul_zero] using
    hpow.const_mul ((ν : ℝ) * ballVolumeConstant ^ (-(2 : ℝ) / 5))

end LiebThirring.TFFunctional

end
