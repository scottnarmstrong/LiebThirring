/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.ProductRegionBasis
public import LiebThirring.TFProduct.WeakContraction
public import LiebThirring.TFProduct.FieldEnergy

/-! # Tensorization of the physical retained-variable form

The only spectral hypothesis is the scalar form identity on the retained
factor. Partial contractions preserve the actual distributional weak
derivatives, and nonnegative sum interchange recovers every product-space
derivative norm.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace LiebThirring.TFProduct
open TFCubes

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

variable {E G ι κ A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [IsLocallyFiniteMeasure (volume : Measure G)]
  [Countable κ] [Fintype A]

/-- A physical scalar factor form identity yields its complete product-space energy identity. -/
theorem hasSum_productRegion_retainedEnergy (Ω : Set E) (Θ : Set G) (hΘ : IsOpen Θ)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω))
    (C : HilbertBasis κ ℂ (RegionState G ℂ Θ))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (d : A → E)
    (hfactor : ∀ (u : RegionState E ℂ Ω) (g : A → RegionState E ℂ Ω),
      (∀ a, HasWeakDerivativeOn Ω (d a) u (g a)) →
      HasSum (fun i => w i * ‖B.repr u i‖ ^ 2) (∑ a : A, ‖g a‖ ^ 2))
    (u : RegionState (E × G) ℂ (Ω ×ˢ Θ))
    (g : A → RegionState (E × G) ℂ (Ω ×ˢ Θ))
    (hweak : ∀ a, HasWeakDerivativeOn (Ω ×ˢ Θ) (d a, 0) u (g a)) :
    HasSum (fun p : ι × κ => w p.1 *
      ‖(productRegionHilbertBasis Ω Θ B C).repr u p‖ ^ 2) (∑ a : A, ‖g a‖ ^ 2) := by
  have hcoeff : ∀ j, HasSum
      (fun i => w i * ‖inner ℂ (B i)
        (fieldCoefficient (volume.restrict Ω) (C j)
          (l2Curry (productRegionToProd Ω Θ u)))‖ ^ 2)
      (∑ a : A, ‖fieldCoefficient (volume.restrict Ω) (C j)
        (l2Curry (productRegionToProd Ω Θ (g a)))‖ ^ 2) := by
    intro j
    have heq (s : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
        partialContraction Ω Θ (C j) s = fieldCoefficient (volume.restrict Ω) (C j)
          (l2Curry (productRegionToProd Ω Θ s)) := rfl
    have h := hfactor (partialContraction Ω Θ (C j) u)
      (fun a => partialContraction Ω Θ (C j) (g a))
      (fun a => hasWeakDerivativeOn_partialContraction Ω Θ hΘ
        (d a) (C j) (hweak a))
    simpa only [HilbertBasis.repr_apply_apply, heq] using h
  have hs := hasSum_weighted_fieldEnergy (volume.restrict Ω) B C w hw
    (l2Curry (productRegionToProd Ω Θ u))
    (fun a => l2Curry (productRegionToProd Ω Θ (g a))) hcoeff
  have ht : HasSum (fun p : ι × κ => w p.1 *
      ‖(productRegionHilbertBasis Ω Θ B C).repr u p‖ ^ 2)
      (∑ a : A, ‖l2Curry (productRegionToProd Ω Θ (g a))‖ ^ 2) :=
    hs.congr_fun fun p => by
      rw [HilbertBasis.repr_apply_apply, inner_productRegionHilbertBasis,
        inner_fieldTensor]
      rfl
  simpa only [l2Curry_norm, productRegionToProd_norm] using ht

end LiebThirring.TFProduct
end
