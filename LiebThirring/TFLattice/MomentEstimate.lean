/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.BallMomentComparison
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic

/-!
# Uniform boundary errors for the sharp lattice squared moments

The leading term is qπt⁵/10 for both boundary conditions. Coordinate-face
modes contribute only a fourth-order error. Source: Lieb–Simon (1977) III.13,
pp. 67–69 (sharp eigenvalue sums).
-/

public section

open scoped NNReal

namespace LiebThirring.TFLattice

theorem sum_squaredRadius_neumannBallModes_error_le (q : ℕ) (t : ℝ≥0) :
    |(∑ p ∈ neumannBallModes q t, (squaredRadius p.1 : ℝ)) -
      (q : ℝ) * (Real.pi / 10) * (t : ℝ) ^ 5| ≤
      (q : ℝ) * (12 * Real.pi) *
        ((t : ℝ) ^ 4 + (t : ℝ) ^ 3 + (t : ℝ) ^ 2 + (t : ℝ) + 1) := by
  have hb := sum_squaredRadius_neumannBallModes_bounds q t
  have ha := (card_neumannBallModes_volume_bounds q t).2
  have hd : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have hp3 := pow_le_pow_left₀ (add_nonneg t.property (Real.sqrt_nonneg 3))
    (add_le_add_right hd (t : ℝ)) 3
  have hp5 := pow_le_pow_left₀ (add_nonneg t.property (Real.sqrt_nonneg 3))
    (add_le_add_right hd (t : ℝ)) 5
  have hA : ((neumannBallModes q t).card : ℝ) ≤
      (q : ℝ) * (Real.pi / 6) * ((t : ℝ) + 2) ^ 3 :=
    ha.trans (mul_le_mul_of_nonneg_left hp3 (by positivity))
  have hL : (2 * Real.sqrt 3 * (t : ℝ) + 3) * (neumannBallModes q t).card ≤
      (4 * (t : ℝ) + 3) * ((q : ℝ) * (Real.pi / 6) * ((t : ℝ) + 2) ^ 3) := by
    apply mul_le_mul _ hA (Nat.cast_nonneg _) (by positivity)
    have h := mul_le_mul_of_nonneg_right hd t.property
    calc
      _ = (Real.sqrt 3 * (t : ℝ)) * 2 + 3 := by ring
      _ ≤ (2 * (t : ℝ)) * 2 + 3 := add_le_add_left
        (mul_le_mul_of_nonneg_right h (by norm_num)) 3
      _ = _ := by ring
  have hLP : (4 * (t : ℝ) + 3) * ((t : ℝ) + 2) ^ 3 ≤
      72 * ((t : ℝ) ^ 4 + (t : ℝ) ^ 3 + (t : ℝ) ^ 2 + (t : ℝ) + 1) := by
    ring_nf
    nlinarith only [t.property, pow_nonneg t.property 2, pow_nonneg t.property 3,
      pow_nonneg t.property 4]
  have hLP' := mul_le_mul_of_nonneg_left hLP
    (show 0 ≤ (q : ℝ) * (Real.pi / 6) by positivity)
  have hU := mul_le_mul_of_nonneg_left hp5
    (show 0 ≤ (q : ℝ) * (Real.pi / 10) by positivity)
  have hUP : ((t : ℝ) + 2) ^ 5 - (t : ℝ) ^ 5 ≤
      120 * ((t : ℝ) ^ 4 + (t : ℝ) ^ 3 + (t : ℝ) ^ 2 + (t : ℝ) + 1) := by
    ring_nf
    nlinarith only [t.property, pow_nonneg t.property 2, pow_nonneg t.property 3,
      pow_nonneg t.property 4]
  have hUP' := mul_le_mul_of_nonneg_left hUP
    (show 0 ≤ (q : ℝ) * (Real.pi / 10) by positivity)
  dsimp only [NNReal.toReal] at *
  apply abs_le.mpr
  constructor
  · nlinarith only [hb.1, hL, hLP']
  · have hU' : (q : ℝ) * (Real.pi / 10 * ((t : ℝ) + Real.sqrt 3) ^ 5) ≤
        (q : ℝ) * (Real.pi / 10 * ((t : ℝ) + 2) ^ 5) := by
      dsimp only [NNReal.toReal] at *
      convert hU using 1 <;> ring
    have h := hb.2.trans hU'
    dsimp only [NNReal.toReal] at *
    nlinarith only [h, hUP']

end LiebThirring.TFLattice

end
