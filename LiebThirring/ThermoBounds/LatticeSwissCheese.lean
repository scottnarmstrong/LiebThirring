/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseRigidCube
public import LiebThirring.Packing.BallLattice
public import LiebThirring.ThermoLimit.CanonicalPackingGeometry
import Mathlib.Tactic

/-!
# Swiss-cheese packings in interior lattice cubes

This module installs a finite truncation of the proved Swiss-cheese construction in every
open lattice cube contained in a bounded region.  Its index set and level sums are the ones
used in the arbitrary-radius thermodynamic comparisons.
-/

public section

open Finset Metric Set

namespace LiebThirring.ThermoBounds

open LiebThirring ThermoLimit

/-- A lattice open cell is a literal translate of the coordinate cube. -/
theorem latticeOpenCell_eq_add_image (ell : ℝ) (z : LatticeIndex) :
    latticeOpenCell ell z = (fun x : Position => latticeCorner ell z + x) ''
      openCoordinateCube ell := by
  ext x
  constructor
  · intro hx
    refine ⟨x - latticeCorner ell z, ?_, by simp⟩
    intro i
    have hi := hx i
    change 0 < x i - ell * (z i : ℝ) ∧ x i - ell * (z i : ℝ) < ell
    constructor <;> linarith only [hi.1, hi.2]
  · rintro ⟨y, hy, rfl⟩ i
    have hi := hy i
    change ell * (z i : ℝ) < ell * (z i : ℝ) + y i ∧
      ell * (z i : ℝ) + y i < ell * ((z i : ℝ) + 1)
    constructor
    · linarith only [hi.1]
    · have he : ell * ((z i : ℝ) + 1) = ell * (z i : ℝ) + ell := by ring
      rw [he]
      linarith only [hi.2]

/-- Put the first `t` Swiss-cheese levels into every interior-eligible lattice cube.
The level-`j` radius is the standard radius `28^(k-j-1)`. -/
theorem exists_lattice_swissCheese_packing {ell : ℝ} (hell : 0 < ell)
    {Ω : Set Position} (hΩ : Bornology.IsBounded Ω) {k t : ℕ} (htk : t ≤ k)
    (hvol : ell ^ 3 = ballVolumeConstant * ((28 : ℝ) ^ k) ^ 3) :
    ∃ c : LatticeIndex × SwissCheeseLabel → Position,
      (∀ p ∈ (interiorLatticeCubes ell Ω hell hΩ).product (swissCheeseLevels t),
        closedBall (c p) ((28 : ℝ) ^ (k - p.2.1 - 1)) ⊆ Ω) ∧
      ((interiorLatticeCubes ell Ω hell hΩ).product
        (swissCheeseLevels t) : Set (LatticeIndex × SwissCheeseLabel)).PairwiseDisjoint
          (fun p => ball (c p) ((28 : ℝ) ^ (k - p.2.1 - 1))) := by
  classical
  have hlocal : ∀ z : LatticeIndex, ∃ c : SwissCheeseLabel → Position,
      (∀ i ∈ swissCheeseLevels t,
        closedBall (c i) ((28 : ℝ) ^ (k - i.1 - 1)) ⊆ latticeOpenCell ell z) ∧
      (swissCheeseLevels t : Set SwissCheeseLabel).PairwiseDisjoint
        (fun i => ball (c i) ((28 : ℝ) ^ (k - i.1 - 1))) := by
    intro z
    obtain ⟨c₀, hc₀, hd₀, _⟩ := exists_swissCheese_rigidCube_complete
      (latticeCorner ell z) (LinearIsometryEquiv.refl ℝ Position) hell
      (pow_pos (by norm_num : (0 : ℝ) < 28) k) hvol
    refine ⟨c₀, ?_, ?_⟩
    · intro i hi
      have hit : i.1 < t := mem_swissCheeseLevels.mp hi
      have hr := hc₀ i
      -- The construction's zero-based level has radius `28^(k-i-1)`.
      have he : (k : ℤ) + (-((i.1 : ℤ) + 1)) = (k - i.1 - 1 : ℕ) := by omega
      have hrad : swissCheeseRadius ((28 : ℝ) ^ k) i.1 =
          (28 : ℝ) ^ (k - i.1 - 1) := by
        unfold swissCheeseRadius
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (28 : ℝ) ≠ 0), he, zpow_natCast]
      rw [hrad] at hr
      simpa [rigidCoordinateCube, latticeOpenCell_eq_add_image,
        LinearIsometryEquiv.coe_refl] using hr
    · intro i hi j hj hij
      have hit : i.1 < t := mem_swissCheeseLevels.mp hi
      have hjt : j.1 < t := mem_swissCheeseLevels.mp hj
      have hei : (k : ℤ) + (-((i.1 : ℤ) + 1)) = (k - i.1 - 1 : ℕ) := by omega
      have hej : (k : ℤ) + (-((j.1 : ℤ) + 1)) = (k - j.1 - 1 : ℕ) := by omega
      have hri : swissCheeseRadius ((28 : ℝ) ^ k) i.1 =
          (28 : ℝ) ^ (k - i.1 - 1) := by
        unfold swissCheeseRadius
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (28 : ℝ) ≠ 0), hei, zpow_natCast]
      have hrj : swissCheeseRadius ((28 : ℝ) ^ k) j.1 =
          (28 : ℝ) ^ (k - j.1 - 1) := by
        unfold swissCheeseRadius
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (28 : ℝ) ≠ 0), hej, zpow_natCast]
      simpa only [hri, hrj] using hd₀ hij
  choose cz hcz using hlocal
  refine ⟨fun p => cz p.1 p.2, ?_, ?_⟩
  · rintro ⟨z, i⟩ hp
    have hp' := Finset.mem_product.mp hp
    exact (hcz z).1 i hp'.2 |>.trans (mem_interiorLatticeCubes.mp hp'.1)
  · rintro ⟨z, i⟩ hp ⟨w, j⟩ hq hpq
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    by_cases hzw : z = w
    · subst w
      have hij : i ≠ j := by
        intro hij
        apply hpq
        simp [hij]
      exact (hcz z).2 hp'.2 hq'.2 hij
    · exact (latticeCell_disjoint hell hzw).mono
        (ball_subset_closedBall.trans
          ((hcz z).1 i hp'.2 |>.trans (latticeOpenCell_subset_cell ell z)))
        (ball_subset_closedBall.trans
          ((hcz w).1 j hq'.2 |>.trans (latticeOpenCell_subset_cell ell w)))

/-- Exact regrouping of a level-dependent sum over all cube/label pairs. -/
theorem sum_lattice_swissCheese_levels {ell : ℝ} (hell : 0 < ell)
    {Ω : Set Position} (hΩ : Bornology.IsBounded Ω) (t : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ (interiorLatticeCubes ell Ω hell hΩ).product (swissCheeseLevels t), g p.2.1 =
      ((interiorLatticeCubes ell Ω hell hΩ).card : ℝ) *
        ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) * g j := by
  calc
    _ = ∑ _z ∈ interiorLatticeCubes ell Ω hell hΩ,
        ∑ i ∈ swissCheeseLevels t, g i.1 := Finset.sum_product _ _ _
    _ = _ := by
      rw [swissCheeseLevels, sum_sigma]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

end LiebThirring.ThermoBounds

end
