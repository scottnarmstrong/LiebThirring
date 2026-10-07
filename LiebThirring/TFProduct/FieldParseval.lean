/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.HilbertField
public import LiebThirring.TFProduct.BasisTransport

/-!
# Parseval for Hilbert-valued L² fields

The squared norms of the coefficient fields of a Hilbert-valued L² function
sum to its squared norm.  The proof applies Parseval to the complete tensor
basis and then sums first over the scalar L² basis.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LiebThirring.TFProduct

variable {X H ι κ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [Countable κ]

/-- Parseval decomposed along a complete basis of the Hilbert-valued fiber. -/
theorem hasSum_norm_sq_fieldCoefficient
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ H)
    (u : Lp H 2 μ) :
    HasSum (fun j => ‖fieldCoefficient μ (C j) u‖ ^ 2) (‖u‖ ^ 2) := by
  let D : HilbertBasis (κ × ι) ℂ (Lp H 2 μ) :=
    reindexHilbertBasis (fieldHilbertBasis μ B C) (Equiv.prodComm κ ι)
  have htotal : HasSum (fun p : κ × ι => ‖inner ℂ (B p.2)
      (fieldCoefficient μ (C p.1) u)‖ ^ 2) (‖u‖ ^ 2) := by
    have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (D.repr u)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, D,
      HilbertBasis.repr_apply_apply, reindexHilbertBasis_apply,
      fieldHilbertBasis_apply, Equiv.prodComm_apply, Prod.swap, inner_fieldTensor,
      LinearIsometryEquiv.norm_map] using h
  apply htotal.prod_fiberwise
  intro j
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (B.repr (fieldCoefficient μ (C j) u))
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] using h

end LiebThirring.TFProduct

end
