/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseStage
import Mathlib.Tactic

/-!
# The successive lattice step of the Swiss-cheese packing

The internal step uses a boundary estimate for the original container. Ball and
cube theorems discharge that geometric estimate before applying this step.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- Actual lattice capacity in the punctured container, at the next scale. -/
theorem swissCheese_remainder_volume_budget {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) (hv : volume.real Ω = ballVolumeConstant)
    {t : ℕ} {c : SwissCheeseLabel → Position} (hc : isSwissCheeseStage Ω t c)
    (hb : volume.real (latticeBoundaryLayer (2 * swissCheeseRadius 1 t) Ω) ≤
      14 * Real.sqrt 3 * ballVolumeConstant * swissCheeseRadius 1 t) :
    (swissCheeseMultiplicity t : ℝ) * (2 * swissCheeseRadius 1 t) ^ 3 ≤
      volume.real (packingRemainder Ω (swissCheeseLevels t) c swissCheeseLabelRadius) -
      volume.real (latticeBoundaryLayer (2 * swissCheeseRadius 1 t)
        (packingRemainder Ω (swissCheeseLevels t) c swissCheeseLabelRadius)) := by
  let r := swissCheeseRadius 1 t
  have hr : 0 ≤ r := (swissCheeseRadius_pos zero_lt_one t).le
  have hp : 0 ≤ (27 : ℝ) ^ t := pow_nonneg (by norm_num) _
  have hcoef : 0 ≤ 14 * Real.sqrt 3 * ballVolumeConstant * r :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      ballVolumeConstant_pos.le) hr
  have hbound := volume_real_packingRemainder_boundaryLayer_le
    (show 0 ≤ 2 * r by positivity) hΩ (swissCheeseLevels t) c swissCheeseLabelRadius
    (fun i _ => (swissCheeseLabelRadius_pos i).le)
    (fun i hi => swissCheese_cell_diameter_le_old (mem_swissCheeseLevels.mp hi))
  have hsum : (∑ i ∈ swissCheeseLevels t,
      7 * ballVolumeConstant * swissCheeseLabelRadius i ^ 2 * (Real.sqrt 3 * (2 * r))) =
      14 * Real.sqrt 3 * ballVolumeConstant * r * ∑ j ∈ Finset.range t, (27 : ℝ) ^ j := by
    calc
      _ = 14 * Real.sqrt 3 * ballVolumeConstant * r *
          ∑ i ∈ swissCheeseLevels t, swissCheeseLabelRadius i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_swissCheeseLabelRadius_square]
  rw [hsum] at hbound
  have hlayer : volume.real (latticeBoundaryLayer (2 * r)
      (packingRemainder Ω (swissCheeseLevels t) c swissCheeseLabelRadius)) ≤
      14 * Real.sqrt 3 * ballVolumeConstant * r * (27 : ℝ) ^ t := by
    calc
      _ ≤ 14 * Real.sqrt 3 * ballVolumeConstant * r +
          14 * Real.sqrt 3 * ballVolumeConstant * r *
            ∑ j ∈ Finset.range t, (27 : ℝ) ^ j := hbound.trans (add_le_add hb le_rfl)
      _ = (14 * Real.sqrt 3 * ballVolumeConstant * r) *
          (1 + ∑ j ∈ Finset.range t, (27 : ℝ) ^ j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_old_surface_multiplicity_real_le t) hcoef
  have hvrem := volume_real_swissCheese_remainder hΩ hv hc
  rw [swissCheese_residual_eq_scale_mul_surface] at hvrem
  have hrdef : r = (28 : ℝ) ^ (-(t + 1 : ℤ)) := by
    simp only [r, swissCheeseRadius, one_mul]
  rw [← hrdef] at hvrem
  have hs : (swissCheeseMultiplicity t : ℝ) * r ^ 2 = (27 : ℝ) ^ t := by
    simpa only [r, swissCheeseRadius, one_mul] using swissCheese_surface_weight t
  calc
    (swissCheeseMultiplicity t : ℝ) * (2 * r) ^ 3 = 8 * r * (27 : ℝ) ^ t := by
      rw [← hs]
      ring
    _ ≤ (ballVolumeConstant * (28 - 14 * Real.sqrt 3)) * (r * (27 : ℝ) ^ t) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        swissCheese_capacity_coefficient (mul_nonneg hr hp)
    _ = ballVolumeConstant * (28 * r * (27 : ℝ) ^ t) -
        14 * Real.sqrt 3 * ballVolumeConstant * r * (27 : ℝ) ^ t := by ring
    _ ≤ _ := by rw [← hvrem]; exact sub_le_sub_left hlayer _

/-- Add precisely the next multiplicity while retaining all earlier centres. -/
theorem exists_swissCheese_next_of_boundary_bound {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) (hv : volume.real Ω = ballVolumeConstant)
    {t : ℕ} {c : SwissCheeseLabel → Position} (hc : isSwissCheeseStage Ω t c)
    (hb : volume.real (latticeBoundaryLayer (2 * swissCheeseRadius 1 t) Ω) ≤
      14 * Real.sqrt 3 * ballVolumeConstant * swissCheeseRadius 1 t) :
    ∃ c' : SwissCheeseLabel → Position,
      isSwissCheeseStage Ω (t + 1) c' ∧ ∀ i ∈ swissCheeseLevels t, c' i = c i := by
  classical
  let r := swissCheeseRadius 1 t
  let rem := packingRemainder Ω (swissCheeseLevels t) c swissCheeseLabelRadius
  have hrem := packingRemainder_isBounded hΩ (swissCheeseLevels t) c swissCheeseLabelRadius
  obtain ⟨new, hnewΩ, hnewdis⟩ := exists_lattice_balls_of_volume_budget
    (show 0 < 2 * r by exact mul_pos (by norm_num) (swissCheeseRadius_pos zero_lt_one t))
    hrem (swissCheeseMultiplicity t) (swissCheese_remainder_volume_budget hΩ hv hc hb)
  have hnew : ∀ i, closedBall (new i) r ⊆ rem := by
    intro i
    simpa only [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)] using hnewΩ i
  have hdnew : Pairwise (fun i j => Disjoint (ball (new i) r) (ball (new j) r)) := by
    simpa only [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)] using hnewdis
  let c' : SwissCheeseLabel → Position := fun i =>
    if h : i.1 = t then new (Fin.cast (congrArg swissCheeseMultiplicity h) i.2) else c i
  have hold : ∀ i ∈ swissCheeseLevels t, c' i = c i := by
    intro i hi
    exact dite_eq_right (ne_of_lt (mem_swissCheeseLevels.mp hi))
  have hnext : ∀ i : Fin (swissCheeseMultiplicity t), c' ⟨t, i⟩ = new i := by
    intro i
    simp only [c', dite_eq_left rfl, Fin.cast_refl, id_eq]
  have hcross : ∀ i : Fin (swissCheeseMultiplicity t), ∀ j ∈ swissCheeseLevels t,
      Disjoint (ball (new i) r) (ball (c j) (swissCheeseLabelRadius j)) := by
    intro i j hj
    apply disjoint_left.mpr
    intro x hxi hxj
    exact (hnew i (ball_subset_closedBall hxi)).2
      (mem_iUnion₂.mpr ⟨j, hj, ball_subset_closedBall hxj⟩)
  refine ⟨c', ⟨?_, ?_⟩, hold⟩
  · intro i hi
    have hit := mem_swissCheeseLevels.mp hi
    by_cases heq : i.1 = t
    · obtain ⟨j, k⟩ := i
      dsimp at heq
      subst j
      rw [hnext]
      exact (hnew k).trans sdiff_subset
    · have hiold : i ∈ swissCheeseLevels t := mem_swissCheeseLevels.mpr (by omega)
      rw [hold i hiold]
      exact hc.1 i hiold
  · intro i hi j hj hij
    change Disjoint (ball (c' i) (swissCheeseLabelRadius i))
      (ball (c' j) (swissCheeseLabelRadius j))
    have hit := mem_swissCheeseLevels.mp hi
    have hjt := mem_swissCheeseLevels.mp hj
    by_cases hiold : i.1 < t <;> by_cases hjold : j.1 < t
    · rw [hold i (mem_swissCheeseLevels.mpr hiold), hold j (mem_swissCheeseLevels.mpr hjold)]
      exact hc.2 (mem_swissCheeseLevels.mpr hiold) (mem_swissCheeseLevels.mpr hjold) hij
    · obtain ⟨k, kj⟩ := j
      have heq : k = t := by dsimp at hjt hjold; omega
      subst k
      rw [hold i (mem_swissCheeseLevels.mpr hiold), hnext]
      exact (hcross kj i (mem_swissCheeseLevels.mpr hiold)).symm
    · obtain ⟨k, ki⟩ := i
      have heq : k = t := by dsimp at hit hiold; omega
      subst k
      rw [hnext, hold j (mem_swissCheeseLevels.mpr hjold)]
      exact hcross ki j (mem_swissCheeseLevels.mpr hjold)
    · obtain ⟨k, ki⟩ := i
      obtain ⟨l, lj⟩ := j
      have hk : k = t := by dsimp at hit hiold; omega
      have hl : l = t := by dsimp at hjt hjold; omega
      subst k
      subst l
      rw [hnext, hnext]
      exact hdnew (by intro heq; subst lj; exact hij rfl)

end LiebThirring

end
