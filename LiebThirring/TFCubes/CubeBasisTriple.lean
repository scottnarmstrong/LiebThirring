/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeBasisTotal

/-! # Three-factor scalar L² Hilbert bases -/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFCubes

variable {X₁ X₂ X₃ ι₁ ι₂ ι₃ : Type*}
  [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {μ₃ : Measure X₃}
  [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite μ₃]
  [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]

/-- Iterated product Hilbert basis for three scalar L² factors. -/
noncomputable def hilbertBasisTripleProduct
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 μ₁))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 μ₂))
    (B₃ : HilbertBasis ι₃ ℂ (Lp ℂ 2 μ₃)) :
    HilbertBasis ((ι₁ × ι₂) × ι₃) ℂ (Lp ℂ 2 ((μ₁.prod μ₂).prod μ₃)) :=
  hilbertBasisProduct (hilbertBasisProduct B₁ B₂) B₃

@[simp]
theorem hilbertBasisTripleProduct_apply
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 μ₁))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 μ₂))
    (B₃ : HilbertBasis ι₃ ℂ (Lp ℂ 2 μ₃)) (p : (ι₁ × ι₂) × ι₃) :
    hilbertBasisTripleProduct B₁ B₂ B₃ p =
      lpProd (lpProd (B₁ p.1.1) (B₂ p.1.2)) (B₃ p.2) := by
  rw [hilbertBasisTripleProduct, hilbertBasisProduct_apply, hilbertBasisProduct_apply]

end LiebThirring.TFCubes

end
