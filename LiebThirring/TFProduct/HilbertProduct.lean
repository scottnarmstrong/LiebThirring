/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.HilbertField
public import LiebThirring.Kinetic.CurryingProductSurjective

/-! # Complete Hilbert bases on product measure spaces

The existing Fubini isometry transports the complete field tensor basis to
the actual product L² carrier. The resulting basis vectors are the literal
products of the two scalar basis representatives almost everywhere.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct

variable {X Y ι κ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
  [SecondCountableTopology (Lp ℂ 2 ν)] [Countable κ]

/-- The complete product basis, with no finite-dimensionality restriction. -/
noncomputable def productHilbertBasis (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) : HilbertBasis (ι × κ) ℂ (Lp ℂ 2 (μ.prod ν)) :=
  HilbertBasis.ofRepr (l2CurryLinearIsometryEquiv.trans (fieldHilbertBasis μ B C).repr)

theorem productHilbertBasis_apply (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (p : ι × κ) :
    productHilbertBasis B C p = l2CurryLinearIsometryEquiv.symm
      (fieldTensor μ (B p.1) (C p.2)) := by
  classical
  rw [← HilbertBasis.repr_symm_single (productHilbertBasis B C) p]
  change l2CurryLinearIsometryEquiv.symm
    ((fieldHilbertBasis μ B C).repr.symm (lp.single 2 p 1)) = _
  rw [HilbertBasis.repr_symm_single, fieldHilbertBasis_apply]

/-- The complete product basis has the literal product representative. -/
theorem productHilbertBasis_ae (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (p : ι × κ) :
    productHilbertBasis B C p =ᵐ[μ.prod ν] fun z => B p.1 z.1 * C p.2 z.2 := by
  have hc := l2CurryLinearIsometryEquiv_apply_ae (productHilbertBasis B C p)
  have hcur : l2CurryLinearIsometryEquiv (productHilbertBasis B C p) =
      fieldTensor μ (B p.1) (C p.2) := by
    rw [productHilbertBasis_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hcur] at hc
  have hm : MeasurableSet {z : X × Y |
      productHilbertBasis B C p z = B p.1 z.1 * C p.2 z.2} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (((Lp.stronglyMeasurable (B p.1)).measurable.comp measurable_fst).mul
        ((Lp.stronglyMeasurable (C p.2)).measurable.comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hc, fieldTensor_ae μ (B p.1) (C p.2)] with x hx ht
  filter_upwards [hx, Lp.coeFn_smul (B p.1 x) (C p.2)] with y hy hs
  rw [← hy, ht, hs]
  rfl

end LiebThirring.TFProduct
end
