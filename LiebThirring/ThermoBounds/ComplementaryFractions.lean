/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.LatticeFractions
public import LiebThirring.ThermoBounds.StandardCover
import Mathlib.Tactic

/-! # Actual complementary lattice fractions at the minimal covering scale -/

public section

open Filter Topology Metric
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

theorem complementary_deficit_eq_fractions {ell L : ℝ} (hell : 0 < ell) (K : ℕ) :
    (ballVolumeConstant * (((28 : ℝ) ^ K) ^ 3 - L ^ 3) -
      annulusLatticeCount ell L ((28 : ℝ) ^ K) hell * ell ^ 3) /
        (ballVolumeConstant * ((28 : ℝ) ^ K) ^ 3) =
      1 - neutralBallVolume L / standardVolume ballVolumeConstant K -
        annulusLatticeCount ell L ((28 : ℝ) ^ K) hell * ell ^ 3 /
          standardVolume ballVolumeConstant K := by
  rw [← neutralBallVolume_standard]
  unfold neutralBallVolume
  have hden : ballVolumeConstant * ((28 : ℝ) ^ K) ^ 3 ≠ 0 :=
    (mul_pos ballVolumeConstant_pos (pow_pos (pow_pos (by norm_num) _) _)).ne'
  rw [mul_sub, sub_div, sub_div, div_self hden]

theorem complementary_fractions_geometry {ell L : ℝ} (hell : 0 < ell) {K : ℕ}
    (hL : 1 < L) (hcover : L ≤ (28 : ℝ) ^ K)
    (hmin : ∀ n : ℕ, L ≤ (28 : ℝ) ^ n → K ≤ n) :
    let W := neutralBallVolume L / standardVolume ballVolumeConstant K
    let U := annulusLatticeCount ell L ((28 : ℝ) ^ K) hell * ell ^ 3 /
      standardVolume ballVolumeConstant K
    (28 : ℝ) ^ (-3 : ℤ) ≤ W ∧ W ≤ 1 ∧
      0 ≤ U ∧ 0 ≤ 1 - W - U ∧ W + U + (1 - W - U) = 1 := by
  have hW := standardCover_volumeFraction_bounds ballVolumeConstant_pos hL hcover hmin
  refine ⟨hW.1.le, hW.2, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hell.le _))
      (standardVolume_pos ballVolumeConstant_pos K).le
  · rw [← complementary_deficit_eq_fractions hell K]
    exact div_nonneg (annulusLatticeCount_deficit_nonneg hell
      (zero_lt_one.trans hL).le hcover)
      (mul_pos ballVolumeConstant_pos (pow_pos (pow_pos (by norm_num) _) _)).le
  · ring

theorem tendsto_complementary_fraction_defect {ell : ℝ} (hell : 0 < ell)
    {L : ℕ → ℝ} {K : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hcover : ∀ j, L j ≤ (28 : ℝ) ^ K j) :
    Tendsto (fun j => 1 - neutralBallVolume (L j) / standardVolume ballVolumeConstant (K j) -
      annulusLatticeCount ell (L j) ((28 : ℝ) ^ K j) hell * ell ^ 3 /
        standardVolume ballVolumeConstant (K j)) atTop (𝓝 0) := by
  have ht := tendsto_standard_complementary_lattice_defect ell hell L K hL
    (Eventually.of_forall hcover)
  simpa only [complementary_deficit_eq_fractions] using ht

end LiebThirring.ThermoBounds

end
