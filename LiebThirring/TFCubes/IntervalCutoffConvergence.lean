/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalTestDensity

/-!
# Local convergence of the compact sine tests

At each interior point the cutoffs eventually equal one on a neighborhood. Thus both their
products with a sine mode and the actual derivatives agree locally with the uncut mode.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace LiebThirring.TFCubes

theorem tendsto_intervalCutoffWidth (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Tendsto (intervalCutoffWidth ℓ) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (ℓ.val / 4 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  ext k
  simp only [intervalCutoffWidth, Function.comp_def, Nat.cast_add, Nat.cast_one]
  field_simp

theorem eventually_intervalInteriorCutoff_eq_one_nhds
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    ∀ᶠ k in atTop, intervalInteriorCutoff ℓ k =ᶠ[𝓝 x] fun _ ↦ 1 := by
  have hl := (tendsto_intervalCutoffWidth ℓ).eventually
    (eventually_lt_nhds (show (0 : ℝ) < x / 2 by linarith [hx.1]))
  have hr := (tendsto_intervalCutoffWidth ℓ).eventually
    (eventually_lt_nhds (show (0 : ℝ) < (ℓ.val - x) / 2 by linarith [hx.2]))
  filter_upwards [hl, hr] with k hk₀ hkℓ
  have hleft : 2 * intervalCutoffWidth ℓ k < x := by linarith
  have hright : x < ℓ.val - 2 * intervalCutoffWidth ℓ k := by linarith
  filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hright] with y hy₀ hyℓ
  exact intervalInteriorCutoff_eq_one ℓ k hy₀.le hyℓ.le

theorem eventually_compactDirichletMode_eq_nhds
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    ∀ᶠ k in atTop, compactDirichletMode ℓ n k =ᶠ[𝓝 x]
      fun y ↦ (dirichletIntervalMode ℓ n y : ℂ) := by
  filter_upwards [eventually_intervalInteriorCutoff_eq_one_nhds ℓ hx] with k hk
  filter_upwards [hk] with y hy
  simp [compactDirichletMode, hy]

theorem tendsto_compactDirichletMode
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    Tendsto (fun k ↦ compactDirichletMode ℓ n k x) atTop
      (𝓝 (dirichletIntervalMode ℓ n x : ℂ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_compactDirichletMode_eq_nhds ℓ n hx] with k hk
  exact hk.self_of_nhds.symm

theorem tendsto_fderiv_compactDirichletMode
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    Tendsto (fun k ↦ fderiv ℝ (compactDirichletMode ℓ n k) x 1) atTop
      (𝓝 (fderiv ℝ (fun y ↦ (dirichletIntervalMode ℓ n y : ℂ)) x 1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_compactDirichletMode_eq_nhds ℓ n hx] with k hk
  exact (congrArg (fun L : ℝ →L[ℝ] ℂ ↦ L 1) hk.fderiv_eq).symm

end LiebThirring.TFCubes

end
