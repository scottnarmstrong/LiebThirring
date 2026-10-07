/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.CurryingProductMap
public import LiebThirring.Kinetic.CurryingTransport
public import LiebThirring.TFCubes.LocalWeakDerivative
public import LiebThirring.TFProduct.HilbertField
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Partial contraction on a product region

This is the bounded map obtained by currying a scalar product L² class and taking its
Hilbert-space coefficient against a fixed spectator state.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Topology

namespace LiebThirring.TFProduct

open TFCubes

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [SFinite (volume : Measure E)]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
  [SFinite (volume : Measure G)] [SecondCountableTopology G]

/-- Regard a class on a product region as a class for the product of the two restricted
measures.  The two measures are equal by `volume_eq_prod` and `prod_restrict`. -/
noncomputable def productRegionToProd (Ω : Set E) (Θ : Set G) :
    RegionState (E × G) ℂ (Ω ×ˢ Θ) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((volume.restrict Ω).prod (volume.restrict Θ)) :=
  l2PullbackEquiv (E := ℂ) (MeasurableEquiv.refl (E × G)) {
    measurable := measurable_id
    map_eq := by
      change Measure.map id ((volume.restrict Ω).prod (volume.restrict Θ)) =
        volume.restrict (Ω ×ˢ Θ)
      rw [Measure.map_id, Measure.prod_restrict, ← Measure.volume_eq_prod] }

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [BorelSpace G]
  [SecondCountableTopology G] in
@[simp] theorem productRegionToProd_norm (Ω : Set E) (Θ : Set G)
    (u : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
    ‖productRegionToProd Ω Θ u‖ = ‖u‖ :=
  (productRegionToProd Ω Θ).norm_map u

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The measure transport does not change representatives. -/
theorem productRegionToProd_ae (Ω : Set E) (Θ : Set G)
    (u : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
    productRegionToProd Ω Θ u =ᵐ[(volume.restrict Ω).prod (volume.restrict Θ)] u := by
  exact
    l2PullbackEquiv_ae (E := ℂ) (MeasurableEquiv.refl (E × G)) ({
      measurable := measurable_id
      map_eq := by
        change Measure.map id ((volume.restrict Ω).prod (volume.restrict Θ)) =
          volume.restrict (Ω ×ˢ Θ)
        rw [Measure.map_id, Measure.prod_restrict, ← Measure.volume_eq_prod] } :
      MeasurePreserving (MeasurableEquiv.refl (E × G))
        ((volume.restrict Ω).prod (volume.restrict Θ))
        (volume.restrict (Ω ×ˢ Θ))) u

/-- Contract the second variable of a scalar L² class on a product region against `φ`. -/
noncomputable def partialContractionCLM (Ω : Set E) (Θ : Set G)
    (φ : RegionState G ℂ Θ) :
    RegionState (E × G) ℂ (Ω ×ˢ Θ) →L[ℂ] RegionState E ℂ Ω :=
  (fieldCoefficient (volume.restrict Ω) φ).comp
    ((l2CurryLinearIsometry (μ := volume.restrict Ω)
      (ν := volume.restrict Θ)).toContinuousLinearMap.comp
        (productRegionToProd Ω Θ).toLinearIsometry.toContinuousLinearMap)

/-- Partial contraction, as an L² vector on the first region. -/
noncomputable def partialContraction (Ω : Set E) (Θ : Set G)
    (φ : RegionState G ℂ Θ) (u : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
    RegionState E ℂ Ω :=
  partialContractionCLM Ω Θ φ u

end LiebThirring.TFProduct

end
