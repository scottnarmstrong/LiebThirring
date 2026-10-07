/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseConstruction
public import LiebThirring.Packing.SwissCheeseVolume
import Mathlib.Tactic

/-!
# Swiss-cheese balls at arbitrary radii and centres

The unit construction transports by a translation and a positive dilation.
-/

public section

open Set MeasureTheory Metric Filter
open scoped Pointwise

namespace LiebThirring

theorem image_ball_affineDilation (a c : Position) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    (fun x : Position => a + R • x) '' ball c r = ball (a + R • c) (R * r) := by
  rw [← image_image (fun x : Position => a + x) (fun x : Position => R • x),
    image_smul, _root_.smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR]
  exact (IsometryEquiv.addLeft a).image_ball (R • c) (R * r)

theorem image_closedBall_affineDilation (a c : Position) {R : ℝ} (hR : 0 < R)
    {r : ℝ} (hr : 0 ≤ r) :
    (fun x : Position => a + R • x) '' closedBall c r =
      closedBall (a + R • c) (R * r) := by
  rw [← image_image (fun x : Position => a + x) (fun x : Position => R • x),
    image_smul, _root_.smul_closedBall R c hr, Real.norm_eq_abs, abs_of_pos hR]
  exact (IsometryEquiv.addLeft a).image_closedBall (R • c) (R * r)

theorem swissCheeseRadius_eq_mul_unit (R : ℝ) (j : ℕ) :
    swissCheeseRadius R j = R * swissCheeseRadius 1 j := by
  simp only [swissCheeseRadius, one_mul]

/-- The required balls at every level in an arbitrary positive-radius ball. -/
theorem exists_swissCheese_ball (a : Position) {R : ℝ} (hR : 0 < R) :
    ∃ c : SwissCheeseLabel → Position,
      (∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ ball a R) ∧
      Pairwise (fun i j => Disjoint (ball (c i) (swissCheeseRadius R i.1))
        (ball (c j) (swissCheeseRadius R j.1))) := by
  obtain ⟨unit, hu⟩ := exists_swissCheese_unitBall
  let f : Position → Position := fun x => a + R • x
  have hfi : Function.Injective f := by
    intro x y hxy
    exact smul_right_injective Position hR.ne' (add_left_cancel hxy)
  have hd := swissCheeseInfinite_pairwiseDisjoint hu
  refine ⟨fun i => f (unit i), ?_, ?_⟩
  · intro i
    rw [swissCheeseRadius_eq_mul_unit, ← image_closedBall_affineDilation a (unit i) hR
      (swissCheeseRadius_pos zero_lt_one _).le]
    have hsub := (hu (i.1 + 1)).1 i (mem_swissCheeseLevels.mpr (Nat.lt_succ_self _))
    have h := image_mono (f := f) hsub
    simpa only [f, swissCheeseLabelRadius, image_ball_affineDilation a 0 hR 1,
      smul_zero, add_zero, mul_one] using h
  · intro i j hij
    have h := disjoint_image_of_injective hfi (hd hij)
    simpa only [f, swissCheeseLabelRadius, image_ball_affineDilation a _ hR,
      swissCheeseRadius, one_mul] using h

/-- The covered set with the actual radii at scale `R`. -/
@[expose] noncomputable def swissCheeseCoveredAtScale (R : ℝ) (t : ℕ)
    (c : SwissCheeseLabel → Position) : Set Position :=
  ⋃ i ∈ swissCheeseLevels t, ball (c i) (swissCheeseRadius R i.1)

/-- Exact finite covered volume at every scale. -/
theorem volume_real_swissCheeseCoveredAtScale {R : ℝ} (hR : 0 < R) (t : ℕ)
    (c : SwissCheeseLabel → Position)
    (hd : Pairwise (fun i j => Disjoint (ball (c i) (swissCheeseRadius R i.1))
      (ball (c j) (swissCheeseRadius R j.1)))) :
    volume.real (swissCheeseCoveredAtScale R t c) =
      ballVolumeConstant * R ^ 3 * (1 - swissCheeseGamma ^ t) := by
  have had : (swissCheeseLevels t : Set SwissCheeseLabel).PairwiseDisjoint
      (fun i => ball (c i) (swissCheeseRadius R i.1)) := fun _ _ _ _ hij => hd hij
  have ht : ∀ i ∈ swissCheeseLevels t, volume (ball (c i) (swissCheeseRadius R i.1)) ≠ ⊤ := by
    intro i _
    rw [volume_ball_position]
    finiteness
  rw [swissCheeseCoveredAtScale, measureReal_biUnion_finset had
    (fun _ _ => measurableSet_ball) ht]
  simp_rw [volume_real_ball_position _ (swissCheeseRadius_pos hR _).le]
  simp only [swissCheeseRadius, mul_pow]
  calc
    _ = R ^ 3 * ∑ i ∈ swissCheeseLevels t, ballVolumeConstant * swissCheeseLabelRadius i ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [swissCheeseLabelRadius, swissCheeseRadius, one_mul]
      ring
    _ = _ := by rw [sum_swissCheeseLabelRadius_cube]; ring

/-- The countable covered family at the requested physical scale. -/
@[expose] noncomputable def swissCheeseInfiniteCoveredAtScale (R : ℝ)
    (c : SwissCheeseLabel → Position) : Set Position :=
  ⋃ i : SwissCheeseLabel, ball (c i) (swissCheeseRadius R i.1)

/-- Full-volume coverage follows from the exact finite identities and `γᵗ → 0`. -/
theorem volume_swissCheeseInfiniteCoveredAtScale {R : ℝ} (hR : 0 < R)
    {Ω : Set Position} (hΩ : Bornology.IsBounded Ω)
    (hv : volume.real Ω = ballVolumeConstant * R ^ 3)
    (c : SwissCheeseLabel → Position)
    (hc : ∀ i, closedBall (c i) (swissCheeseRadius R i.1) ⊆ Ω)
    (hd : Pairwise (fun i j => Disjoint (ball (c i) (swissCheeseRadius R i.1))
      (ball (c j) (swissCheeseRadius R j.1)))) :
    volume (swissCheeseInfiniteCoveredAtScale R c) = volume Ω := by
  have hsub : swissCheeseInfiniteCoveredAtScale R c ⊆ Ω := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact hc i (ball_subset_closedBall hxi)
  have htΩ : volume Ω ≠ ⊤ := hΩ.measure_lt_top.ne
  have htinfty := measure_ne_top_of_subset hsub htΩ
  have hupper : volume.real (swissCheeseInfiniteCoveredAtScale R c) ≤
      ballVolumeConstant * R ^ 3 := by
    rw [← hv]
    exact measureReal_mono hsub htΩ
  have hlower : ballVolumeConstant * R ^ 3 ≤
      volume.real (swissCheeseInfiniteCoveredAtScale R c) := by
    have hconst : Tendsto (fun _t : ℕ => ballVolumeConstant * R ^ 3)
        atTop (nhds (ballVolumeConstant * R ^ 3)) := tendsto_const_nhds
    have hone : Tendsto (fun _t : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have htend := hconst.mul (hone.sub tendsto_swissCheese_residual)
    simp only [sub_zero, mul_one] at htend
    apply le_of_tendsto' htend
    intro t
    rw [← volume_real_swissCheeseCoveredAtScale hR t c hd]
    apply measureReal_mono _ htinfty
    intro x hx
    obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨i, hxi⟩
  apply (ENNReal.toReal_eq_toReal_iff' htinfty htΩ).mp
  change volume.real (swissCheeseInfiniteCoveredAtScale R c) = volume.real Ω
  exact (le_antisymm hupper hlower).trans hv.symm

end LiebThirring

end
