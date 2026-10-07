/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeGeometry

/-!
# Finite lattice selections and their boundary losses

Closed cells entirely inside a bounded region are eligible. Half-open cells
supply the exact counted volume, and the uncovered set is confined to a layer
of thickness `√3 ℓ`. This is the lattice estimate in the ball packing and the
input to lattice boundary estimates (Lieb–Lebowitz (1972) Lemma 3.1, p. 333).
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- Eligible labels: the entire closed cube lies inside the region. -/
@[expose] def eligibleLatticeLabels (ℓ : ℝ) (Ω : Set Position) : Set LatticeIndex :=
  {z | latticeClosedCell ℓ z ⊆ Ω}

/-- The boundary layer described by witnesses in the complement. -/
@[expose] def latticeBoundaryLayer (ℓ : ℝ) (Ω : Set Position) : Set Position :=
  {x | x ∈ Ω ∧ ∃ y, y ∉ Ω ∧ dist x y ≤ Real.sqrt 3 * ℓ}

theorem eligibleLatticeLabels_finite {ℓ : ℝ} (hℓ : 0 < ℓ) {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) : (eligibleLatticeLabels ℓ Ω).Finite := by
  obtain ⟨A, hA⟩ := hΩ.subset_ball (0 : Position)
  refine (Set.Finite.pi (fun _i : Fin 3 =>
    finite_Icc ⌊-A / ℓ⌋ ⌈A / ℓ⌉)).subset ?_
  intro z hz
  have hc := hA (hz (latticeCorner_mem_closedCell hℓ.le z))
  have hn : ‖latticeCorner ℓ z‖ < A := by
    simpa only [mem_ball, dist_zero_right] using hc
  intro i _
  have hi : |ℓ * (z i : ℝ)| ≤ ‖latticeCorner ℓ z‖ := by
    simpa only [latticeCorner, Real.norm_eq_abs] using
      PiLp.norm_apply_le (latticeCorner ℓ z) i
  have hb := abs_le.mp (hi.trans hn.le)
  constructor
  · have hlow : -A / ℓ ≤ (z i : ℝ) :=
      (div_le_iff₀ hℓ).mpr (by simpa only [mul_comm] using hb.1)
    simpa only [Int.floor_intCast] using Int.floor_mono hlow
  · have hhigh : (z i : ℝ) ≤ A / ℓ :=
      (le_div_iff₀ hℓ).mpr (by simpa only [mul_comm] using hb.2)
    simpa only [Int.ceil_intCast] using Int.ceil_mono hhigh

/-- All eligible cubes as a finite set, with no arbitrary witness selection. -/
@[expose] noncomputable def eligibleLatticeCubes (ℓ : ℝ) (Ω : Set Position)
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) : Finset LatticeIndex :=
  (eligibleLatticeLabels_finite hℓ hΩ).toFinset

theorem mem_eligibleLatticeCubes {ℓ : ℝ} {Ω : Set Position}
    {hℓ : 0 < ℓ} {hΩ : Bornology.IsBounded Ω} {z : LatticeIndex} :
    z ∈ eligibleLatticeCubes ℓ Ω hℓ hΩ ↔ latticeClosedCell ℓ z ⊆ Ω :=
  Set.Finite.mem_toFinset _

/-- The counted half-open region of a finite lattice selection. -/
@[expose] def latticeCovered (ℓ : ℝ) (s : Finset LatticeIndex) : Set Position :=
  ⋃ z ∈ s, latticeCell ℓ z

theorem measurableSet_latticeCovered (ℓ : ℝ) (s : Finset LatticeIndex) :
    MeasurableSet (latticeCovered ℓ s) := by
  exact MeasurableSet.biUnion (Set.to_countable _) fun z _ => measurableSet_latticeCell ℓ z

theorem volume_real_latticeCovered {ℓ : ℝ} (hℓ : 0 < ℓ) (s : Finset LatticeIndex) :
    volume.real (latticeCovered ℓ s) = (s.card : ℝ) * ℓ ^ 3 := by
  have hv : ∀ z : LatticeIndex, volume.real (latticeCell ℓ z) = ℓ ^ 3 := by
    intro z
    rw [measureReal_def, volume_latticeCell hℓ.le, ENNReal.toReal_ofReal
      (pow_nonneg hℓ.le _)]
  have hd : (s : Set LatticeIndex).PairwiseDisjoint (latticeCell ℓ) := by
    intro z _ w _ hzw
    exact latticeCell_disjoint hℓ hzw
  have hm : ∀ z ∈ s, MeasurableSet (latticeCell ℓ z) :=
    fun z _ => measurableSet_latticeCell ℓ z
  have ht : ∀ z ∈ s, volume (latticeCell ℓ z) ≠ ⊤ := by
    intro z _
    rw [volume_latticeCell hℓ.le]
    exact ENNReal.ofReal_ne_top
  rw [latticeCovered, measureReal_biUnion_finset hd hm ht]
  simp only [hv, Finset.sum_const, nsmul_eq_mul]

theorem eligible_latticeCovered_subset {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    latticeCovered ℓ (eligibleLatticeCubes ℓ Ω hℓ hΩ) ⊆ Ω := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
  exact (mem_eligibleLatticeCubes.mp hz) (latticeCell_subset_closedCell ℓ z hxz)

/-- Every uncovered point has a complement witness in its own closed cell. -/
theorem lattice_uncovered_subset_boundaryLayer {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    Ω \ latticeCovered ℓ (eligibleLatticeCubes ℓ Ω hℓ hΩ) ⊆
      latticeBoundaryLayer ℓ Ω := by
  classical
  intro x hx
  have hlabel : latticeLabel ℓ x ∉ eligibleLatticeCubes ℓ Ω hℓ hΩ := by
    intro hz
    exact hx.2 (mem_iUnion₂.mpr ⟨latticeLabel ℓ x, hz, mem_latticeCell_label hℓ x⟩)
  have hnot : ¬latticeClosedCell ℓ (latticeLabel ℓ x) ⊆ Ω := by
    exact fun h => hlabel (mem_eligibleLatticeCubes.mpr h)
  obtain ⟨y, hy, hyΩ⟩ := Set.not_subset.mp hnot
  exact ⟨hx.1, y, hyΩ, dist_le_lattice_diameter hℓ.le
    (latticeCell_subset_closedCell ℓ _ (mem_latticeCell_label hℓ x)) hy⟩

/-- LL's lattice counting estimate, with a sharp cube-diameter boundary layer. -/
theorem lattice_volume_deficit_le_boundaryLayer {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    volume.real Ω - ((eligibleLatticeCubes ℓ Ω hℓ hΩ).card : ℝ) * ℓ ^ 3 ≤
      volume.real (latticeBoundaryLayer ℓ Ω) := by
  rw [← volume_real_latticeCovered hℓ, ← measureReal_sdiff
    (eligible_latticeCovered_subset hℓ hΩ) (measurableSet_latticeCovered _ _)
    hΩ.measure_lt_top.ne]
  exact measureReal_mono (lattice_uncovered_subset_boundaryLayer hℓ hΩ)
    (hΩ.subset (fun _ hx => hx.1)).measure_lt_top.ne

/-- Inscribed balls selected by different labels are disjoint. -/
theorem lattice_inscribed_balls_pairwiseDisjoint {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Pairwise (fun z w : LatticeIndex =>
      Disjoint (ball (latticeCenter ℓ z) (ℓ / 2)) (ball (latticeCenter ℓ w) (ℓ / 2))) := by
  intro z w hzw
  exact (latticeCell_disjoint hℓ hzw).mono
    (ball_latticeCenter_subset_cell ℓ z) (ball_latticeCenter_subset_cell ℓ w)

end LiebThirring

end
