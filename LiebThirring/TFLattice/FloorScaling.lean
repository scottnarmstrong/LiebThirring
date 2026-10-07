/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Floor occupations under Thomas–Fermi scaling

Rounding each fixed cube mass down costs less than one particle. The resulting
normalized occupations converge, including a zero cube mass. The exponent
`5/6` is the L² density error exponent in Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
-/

public section

open Filter Topology

namespace LiebThirring.TFLattice

theorem floor_mass_div_bounds {a m : ℝ} (ha : 0 < a) (hm : 0 ≤ m) :
    m - 1 / a ≤ (⌊a * m⌋₊ : ℝ) / a ∧ (⌊a * m⌋₊ : ℝ) / a ≤ m := by
  have hlo := Nat.lt_floor_add_one (a * m)
  have hhi := Nat.floor_le (mul_nonneg ha.le hm)
  constructor
  · apply (le_div_iff₀ ha).mpr
    have he : (m - 1 / a) * a = a * m - 1 := by field_simp
    rw [he]
    linarith
  · exact (div_le_iff₀ ha).mpr (by simpa [mul_comm] using hhi)

theorem tendsto_floor_mass_div {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (fun j => (⌊a j * m⌋₊ : ℝ) / a j) l (𝓝 m) := by
  have hinv : Tendsto (fun j => 1 / a j) l (𝓝 0) := by
    simpa only [Pi.inv_def, one_div] using ha.inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hinv) tendsto_const_nhds
  · filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
    simpa only [one_div] using (floor_mass_div_bounds hj hm).1
  · filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
    exact (floor_mass_div_bounds hj hm).2

theorem tendsto_floor_mass_rpow_div {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun j => (⌊a j * m⌋₊ : ℝ) ^ r / a j) l (𝓝 0) := by
  have hratio := (Real.continuous_rpow_const hr).continuousAt.tendsto.comp
    (tendsto_floor_mass_div ha hm)
  have hdecay : Tendsto (fun j => a j ^ (r - 1)) l (𝓝 0) := by
    have he : -(1 - r) = r - 1 := by ring
    simpa only [Function.comp_def, he] using (tendsto_rpow_neg_atTop (sub_pos.mpr hr1)).comp ha
  have hprod := hratio.mul hdecay
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
  simp only [Function.comp_apply]
  rw [Real.div_rpow (Nat.cast_nonneg _) hj.le, Real.rpow_sub hj]
  simp only [Real.rpow_one]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hj r), hj.ne']

end LiebThirring.TFLattice

end
