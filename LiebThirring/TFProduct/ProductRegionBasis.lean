/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.PartialContraction
public import LiebThirring.TFProduct.HilbertProduct
public import LiebThirring.TFProduct.BasisTransport

/-! # Complete scalar bases on products of physical regions -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace LiebThirring.TFProduct
open TFCubes

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

variable {E G ι κ : Type*} [MeasureSpace E] [MeasureSpace G]
  [SigmaFinite (volume : Measure E)] [SigmaFinite (volume : Measure G)]
  [NormedAddCommGroup G] [BorelSpace G] [SecondCountableTopology G] [Countable κ]

/-- Transport the complete product basis to the literal restricted-volume carrier. -/
noncomputable def productRegionHilbertBasis (Ω : Set E) (Θ : Set G)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω))
    (C : HilbertBasis κ ℂ (RegionState G ℂ Θ)) :
    HilbertBasis (ι × κ) ℂ (RegionState (E × G) ℂ (Ω ×ˢ Θ)) :=
  mapHilbertBasis (productHilbertBasis B C) (productRegionToProd Ω Θ).symm

/-- Literal product representatives on the physical product region. -/
theorem productRegionHilbertBasis_ae (Ω : Set E) (Θ : Set G)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω))
    (C : HilbertBasis κ ℂ (RegionState G ℂ Θ)) (p : ι × κ) :
    productRegionHilbertBasis Ω Θ B C p =ᵐ[volume.restrict (Ω ×ˢ Θ)]
      fun z => B p.1 z.1 * C p.2 z.2 := by
  have h : productRegionToProd Ω Θ (productRegionHilbertBasis Ω Θ B C p) =
      productHilbertBasis B C p := by
    rw [productRegionHilbertBasis, mapHilbertBasis_apply, LinearIsometryEquiv.apply_symm_apply]
  have hp : productRegionHilbertBasis Ω Θ B C p =ᵐ[
      (volume.restrict Ω).prod (volume.restrict Θ)] fun z => B p.1 z.1 * C p.2 z.2 :=
    (productRegionToProd_ae Ω Θ _).symm.trans (by rw [h]; exact productHilbertBasis_ae B C p)
  have hμ : (volume.restrict Ω).prod (volume.restrict Θ) = volume.restrict (Ω ×ˢ Θ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have heq := congrArg (fun μ : Measure (E × G) =>
    (fun z => productRegionHilbertBasis Ω Θ B C p z) =ᵐ[μ]
      (fun z => B p.1 z.1 * C p.2 z.2)) hμ
  exact heq.mp hp

theorem productRegionHilbertBasis_curry_apply (Ω : Set E) (Θ : Set G)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω))
    (C : HilbertBasis κ ℂ (RegionState G ℂ Θ)) (p : ι × κ) :
    l2Curry (productRegionToProd Ω Θ (productRegionHilbertBasis Ω Θ B C p)) =
      fieldTensor (volume.restrict Ω) (B p.1) (C p.2) := by
  rw [productRegionHilbertBasis, mapHilbertBasis_apply,
    LinearIsometryEquiv.apply_symm_apply, productHilbertBasis_apply]
  exact l2CurryLinearIsometryEquiv.apply_symm_apply _

/-- Product-basis coefficients are the scalar basis coefficients of partial contractions. -/
theorem inner_productRegionHilbertBasis (Ω : Set E) (Θ : Set G)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω))
    (C : HilbertBasis κ ℂ (RegionState G ℂ Θ)) (p : ι × κ)
    (u : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
    inner ℂ (productRegionHilbertBasis Ω Θ B C p) u =
      inner ℂ (B p.1) (partialContraction Ω Θ (C p.2) u) := by
  calc
    _ = inner ℂ
        (l2Curry (productRegionToProd Ω Θ (productRegionHilbertBasis Ω Θ B C p)))
        (l2Curry (productRegionToProd Ω Θ u)) := by
      exact ((l2CurryLinearIsometry (μ := volume.restrict Ω)
          (ν := volume.restrict Θ) (E := ℂ)).inner_map_map
        (productRegionToProd Ω Θ (productRegionHilbertBasis Ω Θ B C p))
        (productRegionToProd Ω Θ u)).trans
          ((productRegionToProd Ω Θ).inner_map_map (productRegionHilbertBasis Ω Θ B C p) u) |>.symm
    _ = _ := by
      rw [productRegionHilbertBasis_curry_apply, inner_fieldTensor]
      rfl

end LiebThirring.TFProduct
end
