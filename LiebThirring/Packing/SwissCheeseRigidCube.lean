/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseCube

/-!
# Swiss-cheese packings in arbitrary rigid cubes

The coordinate-cube construction is transported through every Euclidean rigid motion, including
rotations and reflections.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- The image of the coordinate cube of side `A` under `x ↦ a + Q x`. -/
@[expose] def rigidCoordinateCube (a : Position) (Q : Position ≃ₗᵢ[ℝ] Position)
    (A : ℝ) : Set Position :=
  (fun x => a + Q x) '' openCoordinateCube A

/-- Rigid motions preserve the real volume of a coordinate cube. -/
theorem volume_real_rigidCoordinateCube (a : Position) (Q : Position ≃ₗᵢ[ℝ] Position)
    {A : ℝ} (hA : 0 ≤ A) :
    volume.real (rigidCoordinateCube a Q A) = A ^ 3 := by
  let g : Position ≃ᵢ Position := Q.toIsometryEquiv.trans (IsometryEquiv.addLeft a)
  have hgfun : (g : Position → Position) = fun x => a + Q x := rfl
  have hmp : MeasurePreserving (g : Position → Position) volume volume := by
    exact (measurePreserving_add_left volume a).comp Q.measurePreserving
  have hs : MeasurableSet (openCoordinateCube A) := by
    have heval : ∀ i : Fin 3, Measurable (fun x : Position ↦ x i) :=
      fun i ↦ (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).measurable
    change MeasurableSet {x : Position | ∀ i, 0 < x i ∧ x i < A}
    rw [show {x : Position | ∀ i, 0 < x i ∧ x i < A} =
        ⋂ i, {x : Position | 0 < x i} ∩ {x : Position | x i < A} by ext; simp]
    exact MeasurableSet.iInter fun i ↦
      (measurableSet_lt measurable_const (heval i)).inter
        (measurableSet_lt (heval i) measurable_const)
  have hmeas : MeasurableSet (g '' openCoordinateCube A) :=
    g.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  have hmeasure : volume (g '' openCoordinateCube A) = volume (openCoordinateCube A) := by
    have hp := hmp.measure_preimage hmeas.nullMeasurableSet
    rw [g.injective.preimage_image] at hp
    exact hp.symm
  rw [rigidCoordinateCube, ← hgfun, Measure.real, hmeasure]
  exact volume_real_openCoordinateCube hA

/-- Ball packing for an arbitrary translated, rotated, or reflected open cube. -/
theorem exists_swissCheese_rigidCube_complete (a : Position)
    (Q : Position ≃ₗᵢ[ℝ] Position) {A R : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hvol : A ^ 3 = ballVolumeConstant * R ^ 3) :
    ∃ c : SwissCheeseLabel → Position,
      (∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ rigidCoordinateCube a Q A) ∧
      Pairwise (fun i j ↦ Disjoint (ball (c i) (swissCheeseRadius R i.1))
        (ball (c j) (swissCheeseRadius R j.1))) ∧
      (∀ t, volume.real (swissCheeseCoveredAtScale R t c) /
          volume.real (rigidCoordinateCube a Q A) = 1 - swissCheeseGamma ^ t ∧
        volume.real (rigidCoordinateCube a Q A \ swissCheeseCoveredAtScale R t c) /
          volume.real (rigidCoordinateCube a Q A) = swissCheeseGamma ^ t) ∧
      volume (swissCheeseInfiniteCoveredAtScale R c) =
        volume (rigidCoordinateCube a Q A) := by
  obtain ⟨c₀, hc₀, hd₀, _, _⟩ := exists_swissCheese_cube_complete hA hR hvol
  let g : Position ≃ᵢ Position := Q.toIsometryEquiv.trans (IsometryEquiv.addLeft a)
  let c : SwissCheeseLabel → Position := fun i => g (c₀ i)
  have hgfun : (g : Position → Position) = fun x => a + Q x := rfl
  have hc : ∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆
      rigidCoordinateCube a Q A := by
    intro i
    change closedBall (g (c₀ i)) (swissCheeseRadius R i.1) ⊆ rigidCoordinateCube a Q A
    rw [rigidCoordinateCube, ← hgfun, ← g.image_closedBall]
    exact image_mono (hc₀ i)
  have hd : Pairwise (fun i j ↦ Disjoint (ball (c i) (swissCheeseRadius R i.1))
      (ball (c j) (swissCheeseRadius R j.1))) := by
    intro i j hij
    change Disjoint (ball (g (c₀ i)) (swissCheeseRadius R i.1))
      (ball (g (c₀ j)) (swissCheeseRadius R j.1))
    rw [← g.image_ball, ← g.image_ball]
    exact disjoint_image_of_injective g.injective (hd₀ hij)
  have hv : volume.real (rigidCoordinateCube a Q A) = ballVolumeConstant * R ^ 3 := by
    rw [volume_real_rigidCoordinateCube a Q hA.le, hvol]
  have hbounded : Bornology.IsBounded (rigidCoordinateCube a Q A) := by
    rw [rigidCoordinateCube, ← hgfun]
    exact g.isometry.lipschitzWith.isBounded_image (isBounded_openCoordinateCube A)
  have hsub : ∀ t, swissCheeseCoveredAtScale R t c ⊆ rigidCoordinateCube a Q A := by
    intro t x hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
    exact hc i (ball_subset_closedBall hxi)
  have hm : ∀ t, MeasurableSet (swissCheeseCoveredAtScale R t c) := fun t =>
    MeasurableSet.biUnion (Set.to_countable _) (fun _ _ ↦ measurableSet_ball)
  have hvne : ballVolumeConstant * R ^ 3 ≠ 0 :=
    (mul_pos ballVolumeConstant_pos (pow_pos hR _)).ne'
  refine ⟨c, hc, hd, ?_, volume_swissCheeseInfiniteCoveredAtScale hR hbounded hv c hc hd⟩
  intro t
  rw [measureReal_sdiff (hsub t) (hm t) hbounded.measure_lt_top.ne, hv,
    volume_real_swissCheeseCoveredAtScale hR t c hd]
  constructor
  · exact mul_div_cancel_left₀ _ hvne
  · calc
      (ballVolumeConstant * R ^ 3 -
          ballVolumeConstant * R ^ 3 * (1 - swissCheeseGamma ^ t)) /
          (ballVolumeConstant * R ^ 3) = swissCheeseGamma ^ t := by
        have hsimp : ballVolumeConstant * R ^ 3 -
            ballVolumeConstant * R ^ 3 * (1 - swissCheeseGamma ^ t) =
            ballVolumeConstant * R ^ 3 * swissCheeseGamma ^ t := by ring
        rw [hsimp]
        exact mul_div_cancel_left₀ _ hvne

end LiebThirring

end
