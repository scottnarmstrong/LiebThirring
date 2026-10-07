/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FloorScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Powers of floor occupations

Fixed-mass floors preserve the leading semiclassical power and make every
strictly smaller power negligible. Source: Lieb–Simon (1977) III.13–14 (sharp eigenvalue sums/filled-density convergence).
-/

public section

open Filter Topology

namespace LiebThirring.TFLattice

theorem tendsto_floor_mass_rpow_ratio {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun j => (⌊a j * m⌋₊ : ℝ) ^ r / (a j) ^ r) l (𝓝 (m ^ r)) := by
  have ht := (Real.continuous_rpow_const hr).continuousAt.tendsto.comp
    (tendsto_floor_mass_div ha hm)
  apply ht.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
  exact Real.div_rpow (Nat.cast_nonneg _) hj.le r

theorem tendsto_floor_mass_rpow_ratio_zero {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r < t) :
    Tendsto (fun j => (⌊a j * m⌋₊ : ℝ) ^ r / (a j) ^ t) l (𝓝 0) := by
  have hratio := (Real.continuous_rpow_const hr).continuousAt.tendsto.comp
    (tendsto_floor_mass_div ha hm)
  have hdecay : Tendsto (fun j => a j ^ (r - t)) l (𝓝 0) := by
    have he : -(t - r) = r - t := by ring
    simpa only [Function.comp_def, he] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hrt)).comp ha
  have ht := hratio.mul hdecay
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
  simp only [Function.comp_apply]
  rw [Real.div_rpow (Nat.cast_nonneg _) hj.le, Real.rpow_sub hj]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hj r), ne_of_gt (Real.rpow_pos_of_pos hj t)]

end LiebThirring.TFLattice

end
