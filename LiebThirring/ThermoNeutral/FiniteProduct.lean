/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Rotations
public import Mathlib.Probability.Independence.Basic

/-! # Finite products of spatial rotation Haar measure -/

@[expose] public section

open MeasureTheory
open ProbabilityTheory

namespace LiebThirring.ThermoNeutral

/-- Independent Haar rotations indexed by a finite type. -/
noncomputable def productRotationMeasure (ι : Type*) [Fintype ι] :
    Measure (ι → SpatialRotation) :=
  Measure.pi fun _ ↦ spatialRotationMeasure

instance instIsProbabilityMeasureProductRotationMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (productRotationMeasure ι) := by
  unfold productRotationMeasure
  infer_instance

/-- Two distinct coordinates of the finite Haar product have product Haar law. -/
theorem measurePreserving_productRotationMeasure_pair
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun Q : ι → SpatialRotation ↦ (Q i, Q j))
      (productRotationMeasure ι) (spatialRotationMeasure.prod spatialRotationMeasure) := by
  have hind :
      IndepFun (fun Q : ι → SpatialRotation ↦ Q i) (fun Q ↦ Q j)
        (productRotationMeasure ι) :=
    (iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).indepFun hij
  have hei : AEMeasurable (fun Q : ι → SpatialRotation ↦ Q i) (productRotationMeasure ι) := by
    simpa [productRotationMeasure] using
      (measurePreserving_eval (fun _ : ι ↦ spatialRotationMeasure) i).aemeasurable
  have hej : AEMeasurable (fun Q : ι → SpatialRotation ↦ Q j) (productRotationMeasure ι) := by
    simpa [productRotationMeasure] using
      (measurePreserving_eval (fun _ : ι ↦ spatialRotationMeasure) j).aemeasurable
  refine ⟨by fun_prop, ?_⟩
  rw [hind.map_prod_eq_prod_map_map hei hej]
  change (Measure.map (Function.eval i) (Measure.pi fun _ : ι ↦ spatialRotationMeasure)).prod
      (Measure.map (Function.eval j) (Measure.pi fun _ : ι ↦ spatialRotationMeasure)) = _
  rw [(measurePreserving_eval (fun _ : ι ↦ spatialRotationMeasure) i).map_eq,
    (measurePreserving_eval (fun _ : ι ↦ spatialRotationMeasure) j).map_eq]

/-- Integrability of a two-rotation function transports to two distinct coordinates of the
finite Haar product. -/
theorem integrable_productRotationMeasure_comp_pair
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j)
    {f : SpatialRotation × SpatialRotation → ℝ}
    (hf : Integrable f (spatialRotationMeasure.prod spatialRotationMeasure)) :
    Integrable (fun Q : ι → SpatialRotation ↦ f (Q i, Q j))
      (productRotationMeasure ι) := by
  exact (measurePreserving_productRotationMeasure_pair hij).integrable_comp_of_integrable hf

/-- Fubini reduction of a function of two distinct rotations to the double Haar integral. -/
theorem integral_productRotationMeasure_comp_pair
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j)
    {f : SpatialRotation × SpatialRotation → ℝ}
    (hf : Integrable f (spatialRotationMeasure.prod spatialRotationMeasure)) :
    ∫ Q, f (Q i, Q j) ∂productRotationMeasure ι =
      ∫ R, ∫ S, f (R, S) ∂spatialRotationMeasure ∂spatialRotationMeasure := by
  have hp := measurePreserving_productRotationMeasure_pair hij
  calc
    ∫ Q, f (Q i, Q j) ∂productRotationMeasure ι =
        ∫ p, f p ∂(spatialRotationMeasure.prod spatialRotationMeasure) := by
      rw [← hp.map_eq, integral_map]
      · exact hp.measurable.aemeasurable
      · rw [hp.map_eq]
        exact hf.aestronglyMeasurable
    _ = _ := integral_prod f hf

end LiebThirring.ThermoNeutral

end
