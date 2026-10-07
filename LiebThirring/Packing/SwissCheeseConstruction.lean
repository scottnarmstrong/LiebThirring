/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseStep
import Mathlib.Tactic

/-!
# Successive finite and infinite Swiss-cheese packings

The internal construction preserves all centres selected at older levels.
Its ball specialization proves the geometric packing without extra inputs.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- Internal induction for a container with the stated volume and boundary estimates.
The geometric ball and cube specializations prove these estimates themselves. -/
theorem exists_swissCheese_stages_of_container_estimates {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) (hv : volume.real Ω = ballVolumeConstant)
    (hb : ∀ t : ℕ, volume.real (latticeBoundaryLayer (2 * swissCheeseRadius 1 t) Ω) ≤
      14 * Real.sqrt 3 * ballVolumeConstant * swissCheeseRadius 1 t) :
    ∃ c : SwissCheeseLabel → Position, ∀ t, isSwissCheeseStage Ω t c := by
  classical
  let S := fun t => {c : SwissCheeseLabel → Position // isSwissCheeseStage Ω t c}
  have hstep : ∀ t, ∀ c : S t, ∃ c' : S (t + 1),
      ∀ i ∈ swissCheeseLevels t, c'.val i = c.val i := by
    intro t c
    obtain ⟨c', hc', hsame⟩ := exists_swissCheese_next_of_boundary_bound hΩ hv c.property (hb t)
    exact ⟨⟨c', hc'⟩, hsame⟩
  let advance : (t : ℕ) → S t → S (t + 1) := fun t c => (hstep t c).choose
  let seq : (t : ℕ) → S t := Nat.rec
    (⟨fun _ => 0, isSwissCheeseStage_zero Ω _⟩ : S 0) (fun t c => advance t c)
  have hsame : ∀ t, ∀ i ∈ swissCheeseLevels t, (seq (t + 1)).val i = (seq t).val i := by
    intro t i hi
    exact (hstep t (seq t)).choose_spec i hi
  have hstable : ∀ m n, m ≤ n → ∀ i ∈ swissCheeseLevels m,
      (seq n).val i = (seq m).val i := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro i _; rfl
    | succ n hmn ih =>
      intro i hi
      have hin : i ∈ swissCheeseLevels n :=
        mem_swissCheeseLevels.mpr ((mem_swissCheeseLevels.mp hi).trans_le hmn)
      exact (hsame n i hin).trans (ih i hi)
  let c : SwissCheeseLabel → Position := fun i => (seq (i.1 + 1)).val i
  have heq : ∀ t, ∀ i ∈ swissCheeseLevels t, c i = (seq t).val i := by
    intro t i hi
    exact (hstable (i.1 + 1) t (by have := mem_swissCheeseLevels.mp hi; omega)
      i (mem_swissCheeseLevels.mpr (Nat.lt_succ_self _))).symm
  refine ⟨c, ?_⟩
  intro t
  constructor
  · intro i hi
    rw [heq t i hi]
    exact (seq t).property.1 i hi
  · intro i hi j hj hij
    change Disjoint (ball (c i) (swissCheeseLabelRadius i))
      (ball (c j) (swissCheeseLabelRadius j))
    rw [heq t i hi, heq t j hj]
    exact (seq t).property.2 hi hj hij

/-- The unit ball meets the boundary estimate at every step of the construction. -/
theorem swissCheese_unitBall_boundary_estimate (t : ℕ) :
    volume.real (latticeBoundaryLayer (2 * swissCheeseRadius 1 t) (ball (0 : Position) 1)) ≤
      14 * Real.sqrt 3 * ballVolumeConstant * swissCheeseRadius 1 t := by
  have hs := swissCheese_cell_diameter_le_one t
  have hr := (swissCheeseRadius_pos zero_lt_one t).le
  have hh : 0 ≤ Real.sqrt 3 * (2 * swissCheeseRadius 1 t) := by positivity
  calc
    _ ≤ volume.real (ball (0 : Position) 1 \
        ball 0 (1 - Real.sqrt 3 * (2 * swissCheeseRadius 1 t))) :=
      measureReal_mono (latticeBoundaryLayer_ball_subset _)
        (measure_ne_top_of_subset sdiff_subset (by rw [volume_ball_position]; finiteness))
    _ ≤ 3 * ballVolumeConstant * 1 ^ 2 * (Real.sqrt 3 * (2 * swissCheeseRadius 1 t)) :=
      volume_ball_diff_ball_le _ zero_le_one hh hs
    _ ≤ _ := by
      have hcoef : 0 ≤ Real.sqrt 3 * ballVolumeConstant * swissCheeseRadius 1 t :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ballVolumeConstant_pos.le) hr
      nlinarith only [hcoef]

/-- Disjoint balls with all prescribed multiplicities inside the unit ball.
Every finite truncation is obtained from the same family of centres. -/
theorem exists_swissCheese_unitBall :
    ∃ c : SwissCheeseLabel → Position,
      ∀ t, isSwissCheeseStage (ball (0 : Position) 1) t c :=
  exists_swissCheese_stages_of_container_estimates isBounded_ball
    (by rw [volume_real_ball_position _ zero_le_one, one_pow, mul_one])
    swissCheese_unitBall_boundary_estimate

end LiebThirring

end
