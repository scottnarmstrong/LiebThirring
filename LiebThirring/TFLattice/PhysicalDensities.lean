/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.DensityEstimate
public import LiebThirring.Defs.Configuration
import Mathlib.Tactic

/-!
# Density estimates on translated physical cubes

Transport the explicit density formulas to the Euclidean `Position`
carrier. The half-open cube `(b,b+ℓ]³` differs from the open Dirichlet cube
only on a null boundary.
No spectral or one-body-density identification is assumed here.
Source: Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
-/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.TFLattice

noncomputable def cubeCoordinates (b : Position) : Position ≃ᵐ (Fin 3 → ℝ) :=
  (MeasurableEquiv.subRight b).trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm

def cubeCoordinateSet (ℓ : {ℓ : ℝ // 0 < ℓ}) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun _ => Set.Ioc 0 ℓ.val

noncomputable def physicalCube (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) : Set Position :=
  cubeCoordinates b ⁻¹' cubeCoordinateSet ℓ

theorem measurableSet_cubeCoordinateSet (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    MeasurableSet (cubeCoordinateSet ℓ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem measurableSet_physicalCube (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    MeasurableSet (physicalCube ℓ b) :=
  (measurableSet_cubeCoordinateSet ℓ).preimage (cubeCoordinates b).measurable

theorem cubeCoordinateMeasure_eq_restrict (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    cubeCoordinateMeasure ℓ = volume.restrict (cubeCoordinateSet ℓ) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun _ => Set.Ioc 0 ℓ.val)).symm

theorem measurePreserving_cubeCoordinates (b : Position) :
    MeasurePreserving (cubeCoordinates b) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp (measurePreserving_sub_right volume b)

theorem measurePreserving_cubeCoordinates_restrict (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    MeasurePreserving (cubeCoordinates b) (volume.restrict (physicalCube ℓ b))
      (cubeCoordinateMeasure ℓ) := by
  rw [cubeCoordinateMeasure_eq_restrict]
  exact (measurePreserving_cubeCoordinates b).restrict_preimage
    (measurableSet_cubeCoordinateSet ℓ)

/-- Spatial density extended by zero from the translated cube. -/
noncomputable def physicalFilledDensity {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (s : Finset (ModeIndex q)) : Position → ℝ :=
  (physicalCube ℓ b).indicator fun x => filledDensity ℓ s (cubeCoordinates b x)

theorem physicalFilledDensity_nonneg {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (s : Finset (ModeIndex q)) (x : Position) : 0 ≤ physicalFilledDensity ℓ b s x := by
  classical
  by_cases hx : x ∈ physicalCube ℓ b
  · simpa [physicalFilledDensity, hx] using filledDensity_nonneg ℓ s (cubeCoordinates b x)
  · simp [physicalFilledDensity, hx]

end LiebThirring.TFLattice

end
