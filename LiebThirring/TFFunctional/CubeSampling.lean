/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CubeDensities

/-! # Sampling compact continuous densities on finite regular meshes

The literal corner values on eligible half-open cells approximate a compact
continuous function uniformly on a fixed bounded region. Source: step-density approximation.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

/-- A finite mesh whose cell heights are the sampled nonnegative corner values. -/
@[expose] noncomputable def sampledCubeMesh (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset LatticeIndex) : TFUpper.CubeMesh s.card where
  side := ℓ
  label i := ((s.equivFin).symm i).val
  distinct := Subtype.val_injective.comp (s.equivFin).symm.injective
  mass i := ⟨ℓ.val ^ 3 * f (latticeCorner ℓ.val ((s.equivFin).symm i).val),
    mul_nonneg (pow_nonneg ℓ.property.le 3) (hf _)⟩

theorem sampledCubeMesh_label_mem (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset LatticeIndex) (i : Fin s.card) :
    (sampledCubeMesh f hf ℓ s).label i ∈ s := ((s.equivFin).symm i).property

theorem sampledCubeMesh_exists_label (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset LatticeIndex) (z : LatticeIndex) (hz : z ∈ s) :
    ∃ i, (sampledCubeMesh f hf ℓ s).label i = z := by
  refine ⟨s.equivFin ⟨z, hz⟩, ?_⟩
  exact congrArg Subtype.val ((s.equivFin).symm_apply_apply ⟨z, hz⟩)

theorem sampledCubeMesh_stepFunction_of_mem (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset LatticeIndex) (i : Fin s.card)
    (x : Position) (hx : x ∈ latticeCell ℓ.val ((sampledCubeMesh f hf ℓ s).label i)) :
    (sampledCubeMesh f hf ℓ s).stepFunction x =
      f (latticeCorner ℓ.val ((sampledCubeMesh f hf ℓ s).label i)) := by
  classical
  let g := sampledCubeMesh f hf ℓ s
  change g.stepFunction x = _
  unfold TFUpper.CubeMesh.stepFunction
  rw [Finset.sum_eq_single i]
  · have hxg : x ∈ latticeCell g.side.val (g.label i) := hx
    rw [indicator_of_mem hxg]
    change ℓ.val ^ 3 * f (latticeCorner ℓ.val (g.label i)) / ℓ.val ^ 3 = _
    exact mul_div_cancel_left₀ _ (pow_ne_zero 3 ℓ.property.ne')
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji (g.distinct ((latticeLabel_eq_of_mem ℓ.property hj).symm.trans
      (latticeLabel_eq_of_mem ℓ.property hx)))
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem sampledCubeMesh_stepFunction_eq_zero (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset LatticeIndex) (x : Position)
    (hx : latticeLabel ℓ.val x ∉ s) : (sampledCubeMesh f hf ℓ s).stepFunction x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ((latticeLabel_eq_of_mem ℓ.property hi).symm ▸
    sampledCubeMesh_label_mem f hf ℓ s i)

theorem latticeClosedCell_label_subset_ball {ℓ A : ℝ} (hℓ : 0 < ℓ)
    (hsmall : Real.sqrt 3 * ℓ ≤ 2) (x : Position) (hx : x ∈ ball 0 A) :
    latticeClosedCell ℓ (latticeLabel ℓ x) ⊆ ball 0 (A + 3) := by
  intro y hy
  have hd := dist_le_lattice_diameter hℓ.le hy
    (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ x))
  have htri := dist_triangle y x (0 : Position)
  rw [mem_ball] at hx ⊢
  linarith only [hd, hsmall, htri, hx]

/-- Pointwise sampling error; outside the fixed containing ball both terms vanish. -/
theorem sampledCubeMesh_error_le (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (A : ℝ) (hsupport : Function.support f ⊆ ball 0 A)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (hsmall : Real.sqrt 3 * ℓ.val ≤ 2)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hdiam : Real.sqrt 3 * ℓ.val < δ)
    (hmod : ∀ x y : Position, dist x y < δ → dist (f x) (f y) < ε)
    (x : Position) :
    dist ((sampledCubeMesh f hf ℓ
      (eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball)).stepFunction x)
      (f x) ≤ ε := by
  let s := eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball
  by_cases hx : latticeLabel ℓ.val x ∈ s
  · obtain ⟨i, hi⟩ := sampledCubeMesh_exists_label f hf ℓ s _ hx
    have hcell : x ∈ latticeCell ℓ.val ((sampledCubeMesh f hf ℓ s).label i) := by
      rw [hi]
      exact mem_latticeCell_label ℓ.property x
    rw [sampledCubeMesh_stepFunction_of_mem f hf ℓ s i x hcell]
    apply (hmod _ _ ?_).le
    exact (dist_le_lattice_diameter ℓ.property.le
      (latticeCorner_mem_closedCell ℓ.property.le _)
      (latticeCell_subset_closedCell _ _ hcell)).trans_lt hdiam
  · rw [sampledCubeMesh_stepFunction_eq_zero f hf ℓ s x hx]
    have hfzero : f x = 0 := by
      by_contra hn
      have hball := hsupport (Function.mem_support.mpr hn)
      have helig := latticeClosedCell_label_subset_ball ℓ.property hsmall x hball
      exact hx (mem_eligibleLatticeCubes.mpr helig)
    rw [hfzero, dist_self]
    exact hε

theorem sampledCubeMesh_support_subset (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (A : ℝ) (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Function.support ((sampledCubeMesh f hf ℓ
      (eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball)).stepFunction) ⊆
        ball 0 (A + 3) := by
  intro x hx
  by_contra hball
  apply hx
  apply sampledCubeMesh_stepFunction_eq_zero
  intro hi
  have helig := mem_eligibleLatticeCubes.mp hi
  exact hball (helig (latticeCell_subset_closedCell _ _ (mem_latticeCell_label ℓ.property x)))

end LiebThirring.TFFunctional

end
