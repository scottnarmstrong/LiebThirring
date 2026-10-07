/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.BallShells

/-!
# Finite spherical holes and the remaining lattice capacity

Volumes and boundary losses for the induction in the ball packing.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

variable {ι : Type*}

/-- A bounded region after finitely many closed spherical holes have been removed. -/
@[expose] def packingRemainder (Ω : Set Position) (s : Finset ι)
    (c : ι → Position) (r : ι → ℝ) : Set Position :=
  Ω \ ⋃ i ∈ s, closedBall (c i) (r i)

theorem closedBall_ae_eq_ball_position (c : Position) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
  · rw [volume_closedBall_position, volume_ball_position]
  · exact measurableSet_ball.nullMeasurableSet
  · rw [volume_closedBall_position]
    finiteness

/-- Touching boundaries do not change the summed volume of disjoint open balls. -/
theorem volume_real_union_closedBall (s : Finset ι) (c : ι → Position) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hd : (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i))) :
    volume.real (⋃ i ∈ s, closedBall (c i) (r i)) =
      ∑ i ∈ s, ballVolumeConstant * r i ^ 3 := by
  have had : (s : Set ι).Pairwise (fun i j =>
      AEDisjoint volume (closedBall (c i) (r i)) (closedBall (c j) (r j))) := by
    intro i hi j hj hij
    exact (hd hi hj hij).aedisjoint.congr
      (closedBall_ae_eq_ball_position _ _) (closedBall_ae_eq_ball_position _ _)
  have hm : ∀ i ∈ s, NullMeasurableSet (closedBall (c i) (r i)) volume :=
    fun _ _ => measurableSet_closedBall.nullMeasurableSet
  have ht : ∀ i ∈ s, volume (closedBall (c i) (r i)) ≠ ⊤ := by
    intro i _
    rw [volume_closedBall_position]
    finiteness
  rw [measureReal_biUnion_finset₀ had hm ht]
  apply Finset.sum_congr rfl
  intro i hi
  exact volume_real_closedBall_position _ (hr i hi)

theorem packingRemainder_isBounded {Ω : Set Position} (hΩ : Bornology.IsBounded Ω)
    (s : Finset ι) (c : ι → Position) (r : ι → ℝ) :
    Bornology.IsBounded (packingRemainder Ω s c r) :=
  hΩ.subset sdiff_subset

theorem volume_real_packingRemainder {Ω : Set Position} (hΩ : Bornology.IsBounded Ω)
    (s : Finset ι) (c : ι → Position) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hc : ∀ i ∈ s, closedBall (c i) (r i) ⊆ Ω)
    (hd : (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i))) :
    volume.real (packingRemainder Ω s c r) =
      volume.real Ω - ∑ i ∈ s, ballVolumeConstant * r i ^ 3 := by
  have hsub : (⋃ i ∈ s, closedBall (c i) (r i)) ⊆ Ω := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hc i hi hxi
  have hm : MeasurableSet (⋃ i ∈ s, closedBall (c i) (r i)) :=
    MeasurableSet.biUnion (Set.to_countable _) (fun _ _ => measurableSet_closedBall)
  rw [packingRemainder, measureReal_sdiff hsub hm hΩ.measure_lt_top.ne,
    volume_real_union_closedBall s c r hr hd]

/-- Every point near the complement is near the original boundary or an old hole. -/
theorem packingRemainder_boundaryLayer_subset (ℓ : ℝ) (Ω : Set Position)
    (s : Finset ι) (c : ι → Position) (r : ι → ℝ) :
    latticeBoundaryLayer ℓ (packingRemainder Ω s c r) ⊆
      latticeBoundaryLayer ℓ Ω ∪
        ⋃ i ∈ s, closedBall (c i) (r i + Real.sqrt 3 * ℓ) \ closedBall (c i) (r i) := by
  classical
  intro x hx
  obtain ⟨hxΩ, hxholes⟩ := hx.1
  obtain ⟨y, hy, hxy⟩ := hx.2
  by_cases hyΩ : y ∈ Ω
  · have hyholes : y ∈ ⋃ i ∈ s, closedBall (c i) (r i) := by
      by_contra hn
      exact hy ⟨hyΩ, hn⟩
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hyholes
    right
    refine mem_iUnion₂.mpr ⟨i, hi, ?_, ?_⟩
    · apply mem_closedBall.mpr
      calc
        dist x (c i) ≤ dist x y + dist y (c i) := dist_triangle _ _ _
        _ ≤ Real.sqrt 3 * ℓ + r i := add_le_add hxy (mem_closedBall.mp hyi)
        _ = r i + Real.sqrt 3 * ℓ := add_comm _ _
    · intro hxi
      exact hxholes (mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
  · exact Or.inl ⟨hxΩ, y, hyΩ, hxy⟩

/-- Removing finitely many spherical holes adds only their exterior-shell losses. -/
theorem volume_real_packingRemainder_boundaryLayer_le {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) {Ω : Set Position} (hΩ : Bornology.IsBounded Ω)
    (s : Finset ι) (c : ι → Position) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hℓr : ∀ i ∈ s, Real.sqrt 3 * ℓ ≤ r i) :
    volume.real (latticeBoundaryLayer ℓ (packingRemainder Ω s c r)) ≤
      volume.real (latticeBoundaryLayer ℓ Ω) +
        ∑ i ∈ s, 7 * ballVolumeConstant * r i ^ 2 * (Real.sqrt 3 * ℓ) := by
  have hh : 0 ≤ Real.sqrt 3 * ℓ := mul_nonneg (Real.sqrt_nonneg _) hℓ
  let holes := ⋃ i ∈ s, closedBall (c i) (r i + Real.sqrt 3 * ℓ) \ closedBall (c i) (r i)
  have ht : volume (latticeBoundaryLayer ℓ Ω ∪ holes) ≠ ⊤ := by
    apply measure_union_ne_top
    · exact (hΩ.subset (fun _ hx => hx.1)).measure_lt_top.ne
    · apply (measure_biUnion_finset_le _ _).trans_lt ?_ |>.ne
      apply ENNReal.sum_lt_top.mpr
      intro i _
      exact lt_of_le_of_lt (measure_mono sdiff_subset)
        (by rw [volume_closedBall_position]; finiteness)
  calc
    volume.real (latticeBoundaryLayer ℓ (packingRemainder Ω s c r)) ≤
        volume.real (latticeBoundaryLayer ℓ Ω ∪ holes) :=
      measureReal_mono (packingRemainder_boundaryLayer_subset ℓ Ω s c r) ht
    _ ≤ volume.real (latticeBoundaryLayer ℓ Ω) + volume.real holes :=
      measureReal_union_le _ _
    _ ≤ _ := by
      apply add_le_add le_rfl
      exact (measureReal_biUnion_finset_le s (fun i =>
        closedBall (c i) (r i + Real.sqrt 3 * ℓ) \ closedBall (c i) (r i))).trans
        (Finset.sum_le_sum (fun i hi =>
          volume_closedBall_diff_closedBall_le (c i) (hr i hi) hh (hℓr i hi)))

end LiebThirring

end
