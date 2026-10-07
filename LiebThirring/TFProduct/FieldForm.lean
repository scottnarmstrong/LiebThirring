/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.FieldEnergy
public import LiebThirring.TFCubes.CubeSpinWeak

/-! # Scalar form identities extend to Hilbert-valued fields

Bounded coefficient maps preserve distributional weak derivatives. Applying
the scalar form identity and summing the coefficients proves the physical
Hilbert-valued identity, in particular for the complete global spin space.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct
open TFCubes

variable {E H ι κ A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Countable κ] [Fintype A]

/-- A scalar physical form identity extends to a complete Hilbert-valued state carrier. -/
theorem hasSum_weighted_fieldForm (Ω : Set E)
    (B : HilbertBasis ι ℂ (RegionState E ℂ Ω)) (C : HilbertBasis κ ℂ H)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (d : A → E)
    (hfactor : ∀ (u : RegionState E ℂ Ω) (g : A → RegionState E ℂ Ω),
      (∀ a, HasWeakDerivativeOn Ω (d a) u (g a)) →
      HasSum (fun i => w i * ‖B.repr u i‖ ^ 2) (∑ a : A, ‖g a‖ ^ 2))
    (u : RegionState E H Ω) (g : A → RegionState E H Ω)
    (hweak : ∀ a, HasWeakDerivativeOn Ω (d a) u (g a)) :
    HasSum (fun p : ι × κ => w p.1 *
      ‖(fieldHilbertBasis (volume.restrict Ω) B C).repr u p‖ ^ 2)
      (∑ a : A, ‖g a‖ ^ 2) := by
  have hs := hasSum_weighted_fieldEnergy (volume.restrict Ω) B C w hw u g
    (fun j => by
      have h := hfactor (fieldCoefficient (volume.restrict Ω) (C j) u)
        (fun a => fieldCoefficient (volume.restrict Ω) (C j) (g a))
        (fun a => (hweak a).compLpL (innerSL ℂ (C j)))
      simpa only [HilbertBasis.repr_apply_apply] using h)
  simpa only [HilbertBasis.repr_apply_apply, fieldHilbertBasis_apply] using hs

end LiebThirring.TFProduct
end
