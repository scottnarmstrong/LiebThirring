/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseRigidCube
public import LiebThirring.Packing.BallLattice
public import LiebThirring.ThermoLimit.CanonicalAlgebra
import Mathlib.Tactic

/-!
# Minimal standard scales covering an arbitrary radius

The standard radius sequence is `28^K`.  We keep the minimizing index existential, so this
module introduces no public arbitrary-choice definition.  The final theorem records the
vanishing complementary annulus defect for fixed lattice spacing.
-/

public section

open Filter Topology

namespace LiebThirring.ThermoBounds

open LiebThirring ThermoLimit

/-- Every positive radius is covered by a least standard radius. -/
theorem exists_standardCover_index {L : ℝ} (_hL : 0 < L) :
    ∃ K : ℕ, L ≤ (28 : ℝ) ^ K ∧
      ∀ n : ℕ, L ≤ (28 : ℝ) ^ n → K ≤ n := by
  have hex : ∃ n : ℕ, L ≤ (28 : ℝ) ^ n := by
    have ht : Tendsto (fun n : ℕ => (28 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact (ht.eventually (eventually_ge_atTop L)).exists
  let K := Nat.find hex
  refine ⟨K, Nat.find_spec hex, ?_⟩
  intro n hn
  exact Nat.find_min' hex hn

/-- Minimal standard-cover indices are positive once the radius exceeds one. -/
theorem standardCover_index_pos {L : ℝ} {K : ℕ} (hL : 1 < L)
    (hcover : L ≤ (28 : ℝ) ^ K)
    (hmin : ∀ n : ℕ, L ≤ (28 : ℝ) ^ n → K ≤ n) : 0 < K := by
  by_contra hK
  have hK0 : K = 0 := by omega
  subst K
  norm_num at hcover
  exact (not_le_of_gt hL) hcover

/-- Minimality gives the strict lower neighboring-scale inequality. -/
theorem standardCover_prev_lt {L : ℝ} {K : ℕ} (hL : 1 < L)
    (hcover : L ≤ (28 : ℝ) ^ K)
    (hmin : ∀ n : ℕ, L ≤ (28 : ℝ) ^ n → K ≤ n) :
    (28 : ℝ) ^ (K - 1) < L := by
  have hK := standardCover_index_pos hL hcover hmin
  by_contra h
  have hle : L ≤ (28 : ℝ) ^ (K - 1) := le_of_not_gt h
  have := hmin (K - 1) hle
  omega

/-- The target ball occupies strictly more than `28⁻³` and at most all of its minimal
standard covering ball. -/
theorem standardCover_volumeFraction_bounds {σ L : ℝ} {K : ℕ}
    (hσ : 0 < σ) (hL : 1 < L) (hcover : L ≤ (28 : ℝ) ^ K)
    (hmin : ∀ n : ℕ, L ≤ (28 : ℝ) ^ n → K ≤ n) :
    (28 : ℝ) ^ (-3 : ℤ) < σ * L ^ 3 / standardVolume σ K ∧
      σ * L ^ 3 / standardVolume σ K ≤ 1 := by
  have hprev := standardCover_prev_lt hL hcover hmin
  have hK := standardCover_index_pos hL hcover hmin
  have hLK : 0 < (28 : ℝ) ^ K := pow_pos (by norm_num) _
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hpow : (28 : ℝ) ^ (3 * K) = ((28 : ℝ) ^ K) ^ 3 := by
    rw [mul_comm, pow_mul]
  have hprev_eq : (28 : ℝ) ^ (K - 1) = (28 : ℝ) ^ K / 28 := by
    cases K with
    | zero => omega
    | succ n =>
        simp only [Nat.succ_sub_one, pow_succ]
        field_simp
  rw [standardVolume, hpow]
  have hden' : 0 < σ * ((28 : ℝ) ^ K) ^ 3 := mul_pos hσ (pow_pos hLK _)
  constructor
  · rw [zpow_neg]
    rw [hprev_eq] at hprev
    have hcubed : ((28 : ℝ) ^ K / 28) ^ 3 < L ^ 3 := by
      exact pow_lt_pow_left₀ hprev (by positivity) (by norm_num)
    have hscale : ((28 : ℝ) ^ K) ^ 3 < 28 ^ 3 * L ^ 3 := by
      calc
        ((28 : ℝ) ^ K) ^ 3 = 28 ^ 3 * ((28 : ℝ) ^ K / 28) ^ 3 := by
          field_simp
        _ < 28 ^ 3 * L ^ 3 := mul_lt_mul_of_pos_left hcubed (by positivity)
    rw [inv_eq_one_div]
    apply (div_lt_div_iff₀ (by positivity : 0 < (28 : ℝ) ^ 3) hden').2
    nlinarith only [mul_lt_mul_of_pos_left hscale hσ]
  · apply (div_le_one hden').2
    have hcubed : L ^ 3 ≤ ((28 : ℝ) ^ K) ^ 3 := by
      exact pow_le_pow_left₀ hL0.le hcover 3
    exact mul_le_mul_of_nonneg_left hcubed hσ.le

/-- Any family of standard indices whose radii cover radii tending to infinity also tends
to infinity.  In particular this applies to the least indices above. -/
theorem tendsto_standardCover_index_atTop {J : Type*} {l : Filter J}
    (L : J → ℝ) (K : J → ℕ) (hL : Tendsto L l atTop)
    (hcover : ∀ j, L j ≤ (28 : ℝ) ^ K j) : Tendsto K l atTop := by
  rw [tendsto_atTop]
  intro n
  filter_upwards [hL.eventually (eventually_gt_atTop ((28 : ℝ) ^ n))] with j hj
  by_contra hKn
  have hle : K j ≤ n := by omega
  have hp : (28 : ℝ) ^ K j ≤ (28 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hle
  linarith only [hj, hcover j, hp]

/-- The complementary annulus defect tends to zero for fixed lattice spacing and any
standard outer radii covering the growing target radii. -/
theorem tendsto_standard_complementary_lattice_defect {J : Type*} {l : Filter J}
    (ell : ℝ) (hell : 0 < ell) (L : J → ℝ) (K : J → ℕ)
    (hL : Tendsto L l atTop) (hcover : ∀ᶠ j in l, L j ≤ (28 : ℝ) ^ K j) :
    Tendsto (fun j =>
      (ballVolumeConstant * (((28 : ℝ) ^ K j) ^ 3 - L j ^ 3) -
          annulusLatticeCount ell (L j) ((28 : ℝ) ^ K j) hell * ell ^ 3) /
        (ballVolumeConstant * ((28 : ℝ) ^ K j) ^ 3)) l (nhds 0) := by
  exact tendsto_annulusLatticeCount_deficit_normalized ell hell L
    (fun j => (28 : ℝ) ^ K j) hL hcover

end LiebThirring.ThermoBounds

end
