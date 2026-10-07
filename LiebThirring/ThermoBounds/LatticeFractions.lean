/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.Energy
public import LiebThirring.Packing.SwissCheeseRigidCube
public import LiebThirring.Packing.BallLattice
import Mathlib.Tactic

/-!
# Standard cube sides and their occupied fractions

The cube sides are constructed once, before any radius limit. Every
convergence assertion fixes the standard scale, hence the lattice spacing.
-/

public section

open Filter Topology Metric
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

theorem exists_standard_lattice_sides :
    ∃ ell : ℕ → ℝ, ∀ k, 0 < ell k ∧
      (ell k) ^ 3 = standardVolume ballVolumeConstant k := by
  obtain ⟨a, ha, hcube⟩ := exists_cube_side_of_pos ballVolumeConstant_pos
  refine ⟨fun k => a * (28 : ℝ) ^ k, fun k => ⟨mul_pos ha (pow_pos (by norm_num) _), ?_⟩⟩
  rw [mul_pow, hcube]
  unfold standardVolume
  rw [← pow_mul]
  congr 2
  omega

theorem tendsto_ball_lattice_fraction {ell : ℝ} (hell : 0 < ell)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto (fun j => ballLatticeCount ell (L j) hell * ell ^ 3 /
      neutralBallVolume (L j)) atTop (𝓝 1) :=
  (tendsto_ballLatticeCount_normalized ell hell).comp hL

theorem eventually_ball_lattice_count_pos {ell : ℝ} (hell : 0 < ell)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    ∀ᶠ j in atTop, 0 < ballLatticeCount ell (L j) hell := by
  have hμ := tendsto_ball_lattice_fraction hell hL
  have hμpos : ∀ᶠ j in atTop,
      0 < ballLatticeCount ell (L j) hell * ell ^ 3 / neutralBallVolume (L j) :=
    (tendsto_order.1 hμ).1 _ zero_lt_one
  filter_upwards [hμpos] with j hj
  by_contra hn
  have hn0 : ballLatticeCount ell (L j) hell = 0 := by omega
  simp only [hn0, Nat.cast_zero, zero_mul, zero_div, lt_self_iff_false] at hj

end LiebThirring.ThermoBounds

end
