/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.BallRemainder
public import LiebThirring.Packing.LatticeSelection
public import LiebThirring.Packing.SwissCheeseAlgebra
import Mathlib.Tactic

/-!
# Finite stages of the Swiss-cheese construction

Labels carry the source level and one of its prescribed number of copies.
The induction state records geometric containment and disjointness only.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- All ball labels, with zero-based size-class index. -/
abbrev SwissCheeseLabel := (j : ℕ) × Fin (swissCheeseMultiplicity j)

/-- The exact labels in the first `t` size classes. -/
@[expose] noncomputable def swissCheeseLevels (t : ℕ) : Finset SwissCheeseLabel :=
  (Finset.range t).sigma fun _j => Finset.univ

/-- Unit-container radius associated to a ball label. -/
@[expose] noncomputable def swissCheeseLabelRadius (i : SwissCheeseLabel) : ℝ :=
  swissCheeseRadius 1 i.1

theorem mem_swissCheeseLevels {t : ℕ} {i : SwissCheeseLabel} :
    i ∈ swissCheeseLevels t ↔ i.1 < t := by
  simp only [swissCheeseLevels, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_univ, and_true]

/-- The geometric induction state, before the next class is placed. -/
@[expose] def isSwissCheeseStage (Ω : Set Position) (t : ℕ)
    (c : SwissCheeseLabel → Position) : Prop :=
  (∀ i ∈ swissCheeseLevels t, closedBall (c i) (swissCheeseLabelRadius i) ⊆ Ω) ∧
    (swissCheeseLevels t : Set SwissCheeseLabel).PairwiseDisjoint
      (fun i => ball (c i) (swissCheeseLabelRadius i))

theorem isSwissCheeseStage_zero (Ω : Set Position) (c : SwissCheeseLabel → Position) :
    isSwissCheeseStage Ω 0 c := by
  constructor
  · intro i hi
    exact (Nat.not_lt_zero _ (mem_swissCheeseLevels.mp hi)).elim
  · intro i hi
    exact (Nat.not_lt_zero _ (mem_swissCheeseLevels.mp hi)).elim

theorem swissCheeseLabelRadius_pos (i : SwissCheeseLabel) :
    0 < swissCheeseLabelRadius i := swissCheeseRadius_pos zero_lt_one _

/-- Sum of the ball volumes in exactly the first `t` size classes. -/
theorem sum_swissCheeseLabelRadius_cube (t : ℕ) :
    (∑ i ∈ swissCheeseLevels t, ballVolumeConstant * swissCheeseLabelRadius i ^ 3) =
      ballVolumeConstant * (1 - swissCheeseGamma ^ t) := by
  rw [swissCheeseLevels, Finset.sum_sigma]
  simp only [swissCheeseLabelRadius, swissCheeseRadius, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    ∑ j ∈ Finset.range t, (swissCheeseMultiplicity j : ℝ) *
        (ballVolumeConstant * ((28 : ℝ) ^ (-(j + 1 : ℤ))) ^ 3) =
        ballVolumeConstant * ∑ j ∈ Finset.range t,
          (swissCheeseMultiplicity j : ℝ) * ((28 : ℝ) ^ (-(j + 1 : ℤ))) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ballVolumeConstant * (1 - swissCheeseGamma ^ t) := by
      simp_rw [swissCheese_weight]
      rw [sum_swissCheese_weight]

/-- The residual volume at a geometric stage is exactly `σ γᵗ`. -/
theorem volume_real_swissCheese_remainder {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) (hv : volume.real Ω = ballVolumeConstant)
    {t : ℕ} {c : SwissCheeseLabel → Position} (hc : isSwissCheeseStage Ω t c) :
    volume.real (packingRemainder Ω (swissCheeseLevels t) c swissCheeseLabelRadius) =
      ballVolumeConstant * swissCheeseGamma ^ t := by
  rw [volume_real_packingRemainder hΩ _ c swissCheeseLabelRadius
    (fun i _ => (swissCheeseLabelRadius_pos i).le) hc.1 hc.2,
    hv, sum_swissCheeseLabelRadius_cube]
  ring

/-- Surface area weights of all the older size classes. -/
theorem sum_swissCheeseLabelRadius_square (t : ℕ) :
    (∑ i ∈ swissCheeseLevels t, swissCheeseLabelRadius i ^ 2) =
      ∑ j ∈ Finset.range t, (27 : ℝ) ^ j := by
  rw [swissCheeseLevels, Finset.sum_sigma]
  simp only [swissCheeseLabelRadius, swissCheeseRadius, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact swissCheese_surface_weight j

/-- Consecutive radii are separated by the factor `28`. -/
theorem swissCheeseRadius_succ (t : ℕ) :
    28 * swissCheeseRadius 1 (t + 1) = swissCheeseRadius 1 t := by
  simp only [swissCheeseRadius, one_mul]
  calc
    28 * (28 : ℝ) ^ (-(t + 1 + 1 : ℤ)) =
        (28 : ℝ) ^ (1 : ℤ) * (28 : ℝ) ^ (-(t + 1 + 1 : ℤ)) := by rw [zpow_one]
    _ = (28 : ℝ) ^ (1 + -(t + 1 + 1 : ℤ)) :=
      (zpow_add₀ (by norm_num : (28 : ℝ) ≠ 0) _ _).symm
    _ = _ := by congr 1

theorem swissCheeseRadius_antitone : Antitone (swissCheeseRadius 1) := by
  intro j k hjk
  simp only [swissCheeseRadius, one_mul]
  apply zpow_le_zpow_right₀ (by norm_num)
  omega

/-- The cell diameter is smaller than every previous ball radius. -/
theorem swissCheese_cell_diameter_le_old {j t : ℕ} (hjt : j < t) :
    Real.sqrt 3 * (2 * swissCheeseRadius 1 t) ≤ swissCheeseRadius 1 j := by
  have hs : Real.sqrt 3 ≤ (14 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  calc
    Real.sqrt 3 * (2 * swissCheeseRadius 1 t) ≤ 28 * swissCheeseRadius 1 t := by
      have hr := (swissCheeseRadius_pos zero_lt_one t).le
      nlinarith only [hs, hr]
    _ ≤ swissCheeseRadius 1 j := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      rw [swissCheeseRadius_succ]
      exact swissCheeseRadius_antitone (by omega)

/-- The unit container is also larger than the next cell diameter. -/
theorem swissCheese_cell_diameter_le_one (t : ℕ) :
    Real.sqrt 3 * (2 * swissCheeseRadius 1 t) ≤ 1 := by
  have hs : Real.sqrt 3 ≤ (14 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hr := (swissCheeseRadius_pos zero_lt_one t).le
  have ht := swissCheeseRadius_antitone (Nat.zero_le t)
  have hzero : swissCheeseRadius 1 0 = (1 / 28 : ℝ) := by norm_num [swissCheeseRadius]
  rw [hzero] at ht
  nlinarith only [hs, hr, ht]

/-- Numerical room left after the coarse spherical boundary loss. -/
theorem swissCheese_capacity_coefficient :
    8 ≤ ballVolumeConstant * (28 - 14 * Real.sqrt 3) := by
  have h := swissCheese_packing_constant
  have hp := Real.pi_pos
  have hmul := (div_lt_iff₀ hp).mp
    (show 6 / Real.pi < 28 - 14 * Real.sqrt 3 by linarith only [h])
  dsimp [ballVolumeConstant]
  nlinarith only [hmul]

end LiebThirring

end
