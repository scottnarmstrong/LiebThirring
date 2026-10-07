/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Diffuse
public import LiebThirring.TFFunctional.Operations
public import LiebThirring.TFFunctional.DensityBasic

/-! # Kinetic convergence under diffuse mass completion

Adding a diffuse cloud converges in the literal Lp carrier. Source: mass completion.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem tendsto_tfDiffuseDensity (ν : ℝ≥0) :
    Tendsto (fun j => (tfDiffuseDensity ν j).val) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_norm_tfDiffuseDensity ν)

theorem tendsto_kinetic_add_tfDiffuseDensity (ρ : TFDensity) (ν : ℝ≥0) :
    Tendsto (fun j => ∫ x : Position,
      ((tfDensityAdd ρ (tfDiffuseDensity ν j)).val x) ^ ((5 : ℝ) / 3))
      atTop (𝓝 (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3))) := by
  simp_rw [integral_tfDensity_rpow_eq_norm]
  have h : Tendsto (fun j => ρ.val + (tfDiffuseDensity ν j).val) atTop (𝓝 ρ.val) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_tfDiffuseDensity ν)
  exact h.norm.rpow_const (by norm_num)

end LiebThirring.TFFunctional

end
