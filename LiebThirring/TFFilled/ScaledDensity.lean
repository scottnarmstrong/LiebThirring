/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.LpDensity

/-!
# Normalized filled-cube densities with floor occupations

The local L² error is the sum of the oscillatory error and the rounding error.
Both vanish under Thomas–Fermi scaling. No ordering of a degenerate last shell
is required. Source: Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LiebThirring.TFFilled

open LiebThirring.TFLattice

theorem volume_physicalCube_eq (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    volume (physicalCube ℓ b) = (cubeCoordinateMeasure ℓ) univ := by
  have he := (measurePreserving_cubeCoordinates_restrict ℓ b).measure_preimage
    MeasurableSet.univ.nullMeasurableSet
  simpa using he

theorem volume_physicalCube_ne_top (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    volume (physicalCube ℓ b) ≠ ∞ := by
  rw [volume_physicalCube_eq]
  exact measure_ne_top _ _

theorem memLp_physicalCube_const (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : ℝ≥0∞) (c : ℝ) :
    MemLp ((physicalCube ℓ b).indicator (fun _ => c)) p volume :=
  memLp_indicator_const p (measurableSet_physicalCube ℓ b) c
    (Or.inr (volume_physicalCube_ne_top ℓ b))

theorem normalized_density_error_decomposition {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q))
    (a m : ℝ) :
    (fun x => physicalFilledDensity ℓ b s x / a -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) =
    a⁻¹ • (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) +
      (physicalCube ℓ b).indicator (fun _ => ((s.card : ℝ) / a - m) / ℓ.val ^ 3) := by
  classical
  ext x
  by_cases hx : x ∈ physicalCube ℓ b
  · simp only [hx, indicator_of_mem, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [div_eq_mul_inv]
    ring
  · simp [physicalFilledDensity, hx]

theorem memLp_normalized_physicalFilledDensity_sub_two {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q))
    (a m : ℝ) :
    MemLp (fun x => physicalFilledDensity ℓ b s x / a -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) 2 volume := by
  rw [normalized_density_error_decomposition ℓ b s a m]
  exact ((memLp_physicalFilledDensity_sub_two ℓ b s).const_smul a⁻¹).add
    (memLp_physicalCube_const ℓ b 2 _)

end LiebThirring.TFFilled

end
