/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Hilbert bases of Hilbert-valued L² fields

Tensoring a scalar L² basis with a countable Hilbert basis gives a complete
orthonormal family. Completeness is proved by scalar coefficient fields and
the vanishing orthogonal complement, without finite-dimensional tensor bases.
-/

@[expose] public section
open MeasureTheory Submodule Set
open scoped InnerProductSpace
namespace LiebThirring.TFProduct

variable {X H ι κ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X)

/-- The literal field `x ↦ f x • v`. -/
noncomputable def fieldTensor (f : Lp ℂ 2 μ) (v : H) : Lp H 2 μ :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight v).compLp f

theorem fieldTensor_ae (f : Lp ℂ 2 μ) (v : H) :
    fieldTensor μ f v =ᵐ[μ] fun x => f x • v :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight v).coeFn_compLp f

/-- Projection onto the coefficient of a fixed vector. -/
noncomputable def fieldCoefficient (v : H) : Lp H 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (innerSL ℂ v).compLpL 2 μ

theorem fieldCoefficient_ae (v : H) (u : Lp H 2 μ) :
    fieldCoefficient μ v u =ᵐ[μ] fun x => inner ℂ v (u x) :=
  (innerSL ℂ v).coeFn_compLpL u

theorem inner_fieldTensor (f : Lp ℂ 2 μ) (v : H) (u : Lp H 2 μ) :
    inner ℂ (fieldTensor μ f v) u = inner ℂ f (fieldCoefficient μ v u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldTensor_ae μ f v, fieldCoefficient_ae μ v u] with x hf hu
  simp only [hf, hu, inner_smul_left, RCLike.inner_apply']

theorem inner_fieldTensor_fieldTensor (f g : Lp ℂ 2 μ) (v w : H) :
    inner ℂ (fieldTensor μ f v) (fieldTensor μ g w) =
      inner ℂ f g * inner ℂ v w := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [fieldTensor_ae μ f v, fieldTensor_ae μ g w] with x hf hg
  simp only [hf, hg, inner_smul_left, inner_smul_right, RCLike.inner_apply',
    mul_assoc, mul_left_comm]

theorem orthonormal_fieldTensor (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (C : HilbertBasis κ ℂ H) :
    Orthonormal ℂ (fun p : ι × κ => fieldTensor μ (B p.1) (C p.2)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨i', j'⟩
  rw [inner_fieldTensor_fieldTensor,
    orthonormal_iff_ite.mp B.orthonormal i i',
    orthonormal_iff_ite.mp C.orthonormal j j']
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj]

/-- Every coefficient field vanishes for a vector orthogonal to all tensors. -/
theorem fieldTensor_span_orthogonal_eq_bot [Countable κ]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ H) :
    (span ℂ (range (fun p : ι × κ => fieldTensor μ (B p.1) (C p.2))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [mem_bot]
  have hc : ∀ j, fieldCoefficient μ (C j) u = 0 := by
    intro j
    apply B.repr.injective
    ext i
    rw [B.repr_apply_apply, LinearIsometryEquiv.map_zero]
    exact (inner_fieldTensor μ (B i) (C j) u).symm.trans
      (inner_right_of_mem_orthogonal (subset_span (mem_range_self (i, j))) hu)
  apply Lp.ext
  filter_upwards [eventually_countable_forall.mpr (fun j =>
    (fieldCoefficient_ae μ (C j) u).symm.trans (by
      rw [hc j])), Lp.coeFn_zero H 2 μ, Lp.coeFn_zero ℂ 2 μ]
    with x hx hzero hscalar
  rw [hzero]
  change u x = (0 : H)
  apply C.repr.injective
  ext j
  rw [C.repr_apply_apply, LinearIsometryEquiv.map_zero]
  simpa only [Pi.zero_apply, lp.coeFn_zero] using (hx j).trans hscalar

/-- The complete Hilbert basis of literal tensor fields. -/
noncomputable def fieldHilbertBasis [CompleteSpace H] [Countable κ]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ H) :
    HilbertBasis (ι × κ) ℂ (Lp H 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_fieldTensor μ B C)
    (fieldTensor_span_orthogonal_eq_bot μ B C)

@[simp] theorem fieldHilbertBasis_apply [CompleteSpace H] [Countable κ]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ H) (p : ι × κ) :
    fieldHilbertBasis μ B C p = fieldTensor μ (B p.1) (C p.2) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) p

end LiebThirring.TFProduct
end
