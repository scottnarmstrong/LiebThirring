/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.IntegerPhysics
public import LiebThirring.ThermoBounds.TruncatedAlgebra
public import LiebThirring.ThermoBounds.LatticeSwissCheese
public import LiebThirring.ThermoBounds.ComparisonLimits
import Mathlib.Tactic

/-!
# Finite upper comparison from the actual lattice packing

Interior packing comparison before taking limits. Every physical input is an integer energy law
from rigid-motion and domain-inclusion identities and neutral variational packing. The finite geometric family and its exact real budget
are constructed in the proof, and coupled integer interpolation supplies exact integer rounding.
-/

public section

open Finset Metric Set
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

/-- The finite interior comparison used in interior packing comparison. Its hypotheses are the
integer physical laws; neither a packing witness nor a comparison is assumed. -/
theorem finite_lattice_upper_of_integer_inputs
    {E : Set Position → ℕ → ℝ}
    (hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ m, E Ω' m ≤ E Ω m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (ι : Type) (s : Finset ι) (c : ι → Position)
      (r : ι → ℝ) (m : ι → ℕ), s.Nonempty →
      (∀ i ∈ s, 0 < r i) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (⋃ i ∈ s, ball (c i) (r i)) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    {ell L : ℝ} (hell : 0 < ell) (hL : 0 < L) {k t : ℕ}
    (ht : 1 ≤ t) (htk : t < k)
    (hvol : ell ^ 3 = standardVolume ballVolumeConstant k)
    (m : ℕ) (hn : 0 < ballLatticeCount ell L hell) :
    neutralBallDensity E L m ≤
      (ballLatticeCount ell L hell * ell ^ 3 / neutralBallVolume L) *
        ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
          neutralStandardSequence E (k - j - 1)
            ((m : ℝ) / (retainedFraction t * ballLatticeCount ell L hell * ell ^ 3)) := by
  classical
  let S := (interiorLatticeCubes ell (ball (0 : Position) L) hell isBounded_ball).product
    (swissCheeseLevels t)
  let r : LatticeIndex × SwissCheeseLabel → ℝ := fun p => (28 : ℝ) ^ (k - p.2.1 - 1)
  let n : ℕ := ballLatticeCount ell L hell
  let V : ℝ := standardVolume ballVolumeConstant k
  let d : ℝ := (m : ℝ) / (retainedFraction t * n * V)
  let x : LatticeIndex × SwissCheeseLabel → ℝ := fun p =>
    d * standardVolume ballVolumeConstant (k - p.2.1 - 1)
  have hV : 0 < V := standardVolume_pos ballVolumeConstant_pos k
  have hden : 0 < retainedFraction t * (n : ℝ) * V :=
    mul_pos (mul_pos (retainedFraction_pos ht) (Nat.cast_pos.mpr hn)) hV
  have hd : 0 ≤ d := div_nonneg (Nat.cast_nonneg m) hden.le
  have hgeom : ell ^ 3 = ballVolumeConstant * ((28 : ℝ) ^ k) ^ 3 := by
    rw [hvol, ← neutralBallVolume_standard]
    rfl
  obtain ⟨c, hc, hdisj⟩ := exists_lattice_swissCheese_packing hell isBounded_ball htk.le hgeom
  have hS : S.Nonempty := by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hn
    let i : SwissCheeseLabel := ⟨0, ⟨0, swissCheeseMultiplicity_pos 0⟩⟩
    refine ⟨(z, i), mem_product.mpr ⟨hz, ?_⟩⟩
    exact mem_swissCheeseLevels.mpr (by dsimp [i]; omega)
  have hpos : ∀ p ∈ S, 0 < r p := fun _ _ => pow_pos (by norm_num) _
  have hsub : ∀ p ∈ S, ball (c p) (r p) ⊆ ball (0 : Position) L :=
    fun p hp => ball_subset_closedBall.trans (hc p hp)
  have hx : ∀ p ∈ S, 0 ≤ x p := fun p _ =>
    mul_nonneg hd (standardVolume_pos ballVolumeConstant_pos _).le
  have hp := interpolate_ball_packing_of_integer_inputs hmono htranslation
    (hpacking (LatticeIndex × SwissCheeseLabel)) S c r x L hS hL hpos hsub hdisj hx
  have hbudget : (∑ p ∈ S, x p) = (m : ℝ) := by
    rw [show (∑ p ∈ S, x p) = (n : ℝ) *
        ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
          (d * standardVolume ballVolumeConstant (k - j - 1)) from
      sum_lattice_swissCheese_levels hell isBounded_ball t
        (fun j => d * standardVolume ballVolumeConstant (k - j - 1))]
    rw [sum_truncatedBudget htk.le]
    change (n : ℝ) * (d * V * retainedFraction t) = m
    calc
      (n : ℝ) * (d * V * retainedFraction t) =
          d * (retainedFraction t * n * V) := by ring
      _ = m := div_mul_cancel₀ _ hden.ne'
  have henergy : (∑ p ∈ S, interpolate (E (ball (0 : Position) (r p))) (x p)) =
      (n : ℝ) * (V * ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
        neutralStandardSequence E (k - j - 1) d) := by
    rw [show (∑ p ∈ S, interpolate (E (ball (0 : Position) (r p))) (x p)) =
        (n : ℝ) * ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
          interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - j - 1))))
            (d * standardVolume ballVolumeConstant (k - j - 1)) from
      sum_lattice_swissCheese_levels (Ω := ball (0 : Position) L) hell isBounded_ball t
        (fun j => interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - j - 1))))
          (d * standardVolume ballVolumeConstant (k - j - 1)))]
    rw [sum_truncatedEnergy htk]
  rw [hbudget, interpolate_nat, henergy] at hp
  have hnorm := div_le_div_of_nonneg_right hp (neutralBallVolume_pos hL).le
  change neutralBallDensity E L m ≤ _ at hnorm
  have hVeq : V = ell ^ 3 := hvol.symm
  have hdeq : d = (m : ℝ) / (retainedFraction t * n * ell ^ 3) := by
    dsimp only [d]
    rw [hVeq]
  calc
    _ ≤ (n : ℝ) * (V * ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
        neutralStandardSequence E (k - j - 1) d) / neutralBallVolume L := hnorm
    _ = _ := by rw [hVeq, hdeq]; dsimp only [n]; ring

end LiebThirring.ThermoBounds

end
