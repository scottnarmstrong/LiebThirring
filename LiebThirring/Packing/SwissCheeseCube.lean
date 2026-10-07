/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.CubeShells
public import LiebThirring.Packing.SwissCheeseScaling
import Mathlib.Tactic

/-!
# Swiss-cheese packings in cubes

The unit-volume normalization has cube volume equal to the volume of the unit ball. A positive
dilation supplies the packing in every cube whose volume is `ballVolumeConstant * R^3`.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

theorem one_lt_ballVolumeConstant : 1 < ballVolumeConstant := by
  dsimp [ballVolumeConstant]
  nlinarith [Real.pi_gt_three]

/-- All finite stages of the Swiss-cheese packing in a normalized cube. -/
theorem exists_swissCheese_unitCube {A : ℝ} (hA : 0 < A)
    (hvol : A ^ 3 = ballVolumeConstant) :
    ∃ c : SwissCheeseLabel → Position,
      ∀ t, isSwissCheeseStage (openCoordinateCube A) t c := by
  have hAone : 1 ≤ A := by
    by_contra hnot
    have hAlt : A < 1 := lt_of_not_ge hnot
    have : A ^ 3 < 1 := by nlinarith [sq_nonneg A]
    nlinarith [one_lt_ballVolumeConstant]
  apply exists_swissCheese_stages_of_container_estimates (isBounded_openCoordinateCube A)
  · rw [volume_real_openCoordinateCube hA.le, hvol]
  · intro t
    exact volume_real_latticeBoundaryLayer_openCoordinateCube_two_mul_le
      hAone hvol (swissCheeseRadius_pos zero_lt_one t).le

/-- The required infinite family in an arbitrary positive-scale coordinate cube. -/
theorem exists_swissCheese_cube {A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hvol : A ^ 3 = ballVolumeConstant * R ^ 3) :
    ∃ c : SwissCheeseLabel → Position,
      (∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ openCoordinateCube A) ∧
      Pairwise (fun i j ↦ Disjoint (ball (c i) (swissCheeseRadius R i.1))
        (ball (c j) (swissCheeseRadius R j.1))) := by
  have hunitA : 0 < A / R := div_pos hA hR
  have hunitVol : (A / R) ^ 3 = ballVolumeConstant := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 3 hR.ne')).2
    nlinarith [hvol]
  obtain ⟨unit, hu⟩ := exists_swissCheese_unitCube hunitA hunitVol
  let f : Position → Position := fun x ↦ R • x
  have hfi : Function.Injective f := smul_right_injective Position hR.ne'
  have hd := swissCheeseInfinite_pairwiseDisjoint hu
  refine ⟨fun i ↦ f (unit i), ?_, ?_⟩
  · intro i
    change closedBall (R • unit i) (swissCheeseRadius R i.1) ⊆ openCoordinateCube A
    rw [swissCheeseRadius_eq_mul_unit]
    have himage := image_closedBall_affineDilation 0 (unit i) hR
      (swissCheeseRadius_pos zero_lt_one i.1).le
    simp only [zero_add] at himage
    rw [← himage]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxCube := (hu (i.1 + 1)).1 i
      (mem_swissCheeseLevels.mpr (Nat.lt_succ_self _)) hx
    intro k
    have hk := hxCube k
    simp only [smul_eq_mul, PiLp.smul_apply]
    constructor
    · exact mul_pos hR hk.1
    · calc
        R * x k < R * (A / R) := mul_lt_mul_of_pos_left hk.2 hR
        _ = A := by field_simp
  · intro i j hij
    have hi := image_ball_affineDilation 0 (unit i) hR (swissCheeseRadius 1 i.1)
    have hj := image_ball_affineDilation 0 (unit j) hR (swissCheeseRadius 1 j.1)
    simp only [zero_add] at hi hj
    have himg := disjoint_image_of_injective hfi (hd hij)
    change Disjoint ((fun a : Position ↦ R • a) '' ball (unit i) (swissCheeseRadius 1 i.1))
      ((fun a : Position ↦ R • a) '' ball (unit j) (swissCheeseRadius 1 j.1)) at himg
    rw [hi, hj] at himg
    dsimp only [f]
    rw [swissCheeseRadius_eq_mul_unit R i.1, swissCheeseRadius_eq_mul_unit R j.1]
    exact himg

/-- Exact volume of the scale-`R` coordinate cube. -/
theorem volume_real_openCoordinateCube_of_cube_scale {A R : ℝ} (hA : 0 ≤ A)
    (hvol : A ^ 3 = ballVolumeConstant * R ^ 3) :
    volume.real (openCoordinateCube A) = ballVolumeConstant * R ^ 3 := by
  rw [volume_real_openCoordinateCube hA, hvol]

/-- Exact occupied and unfilled fractions in a scale-`R` coordinate cube. -/
theorem swissCheese_cube_fractions {A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hvol : A ^ 3 = ballVolumeConstant * R ^ 3) (t : ℕ)
    (c : SwissCheeseLabel → Position)
    (hc : ∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ openCoordinateCube A)
    (hd : Pairwise (fun i j ↦ Disjoint (ball (c i) (swissCheeseRadius R i.1))
      (ball (c j) (swissCheeseRadius R j.1)))) :
    volume.real (swissCheeseCoveredAtScale R t c) / volume.real (openCoordinateCube A) =
        1 - swissCheeseGamma ^ t ∧
      volume.real (openCoordinateCube A \ swissCheeseCoveredAtScale R t c) /
          volume.real (openCoordinateCube A) = swissCheeseGamma ^ t := by
  have hsub : swissCheeseCoveredAtScale R t c ⊆ openCoordinateCube A := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
    exact hc i (ball_subset_closedBall hxi)
  have hm : MeasurableSet (swissCheeseCoveredAtScale R t c) :=
    MeasurableSet.biUnion (Set.to_countable _) (fun _ _ ↦ measurableSet_ball)
  have hv : volume.real (openCoordinateCube A) = ballVolumeConstant * R ^ 3 :=
    volume_real_openCoordinateCube_of_cube_scale hA.le hvol
  have hvne : ballVolumeConstant * R ^ 3 ≠ 0 :=
    (mul_pos ballVolumeConstant_pos (pow_pos hR _)).ne'
  rw [measureReal_sdiff hsub hm (isBounded_openCoordinateCube A).measure_lt_top.ne,
    hv, volume_real_swissCheeseCoveredAtScale hR t c hd]
  constructor
  · exact mul_div_cancel_left₀ _ hvne
  · calc
      (ballVolumeConstant * R ^ 3 -
          ballVolumeConstant * R ^ 3 * (1 - swissCheeseGamma ^ t)) /
          (ballVolumeConstant * R ^ 3) =
          (ballVolumeConstant * R ^ 3) * swissCheeseGamma ^ t /
            (ballVolumeConstant * R ^ 3) := by ring
      _ = swissCheeseGamma ^ t := mul_div_cancel_left₀ _ hvne

/-- Ball packing for an axis-aligned cube: finite fractions and complete infinite volume coverage. -/
theorem exists_swissCheese_cube_complete {A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hvol : A ^ 3 = ballVolumeConstant * R ^ 3) :
    ∃ c : SwissCheeseLabel → Position,
      (∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ openCoordinateCube A) ∧
      Pairwise (fun i j ↦ Disjoint (ball (c i) (swissCheeseRadius R i.1))
        (ball (c j) (swissCheeseRadius R j.1))) ∧
      (∀ t, volume.real (swissCheeseCoveredAtScale R t c) /
          volume.real (openCoordinateCube A) = 1 - swissCheeseGamma ^ t ∧
        volume.real (openCoordinateCube A \ swissCheeseCoveredAtScale R t c) /
          volume.real (openCoordinateCube A) = swissCheeseGamma ^ t) ∧
      volume (swissCheeseInfiniteCoveredAtScale R c) = volume (openCoordinateCube A) := by
  obtain ⟨c, hc, hd⟩ := exists_swissCheese_cube hA hR hvol
  refine ⟨c, hc, hd, fun t ↦ swissCheese_cube_fractions hA hR hvol t c hc hd, ?_⟩
  exact volume_swissCheeseInfiniteCoveredAtScale hR (isBounded_openCoordinateCube A)
    (volume_real_openCoordinateCube_of_cube_scale hA.le hvol) c hc hd

end LiebThirring

end
