/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Product tests for partial contraction

The weak derivative of a partial contraction is tested with the literal product of a test in
the retained variable and a smooth compactly supported spectator.
-/

@[expose] public section

open Set
open scoped ContDiff Topology

namespace LiebThirring.TFProduct

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The scalar product test `(x,y) ↦ η x * ψ y`. -/
def contractionProductTest (η : E → ℂ) (ψ : G → ℂ) : E × G → ℂ :=
  fun z => η z.1 * ψ z.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem support_contractionProductTest_subset (η : E → ℂ) (ψ : G → ℂ) :
    Function.support (contractionProductTest η ψ) ⊆
      Function.support η ×ˢ Function.support ψ := by
  rintro ⟨x, y⟩ hxy
  simp only [contractionProductTest, Function.mem_support, ne_eq] at hxy ⊢
  exact ⟨fun hx => hxy (by rw [hx, zero_mul]),
    fun hy => hxy (by rw [hy, mul_zero])⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
theorem tsupport_contractionProductTest_subset (η : E → ℂ) (ψ : G → ℂ) :
    tsupport (contractionProductTest η ψ) ⊆ tsupport η ×ˢ tsupport ψ := by
  rw [tsupport]
  refine closure_minimal ((support_contractionProductTest_subset η ψ).trans
    (prod_mono (subset_tsupport η) (subset_tsupport ψ))) ?_
  exact isClosed_closure.prod isClosed_closure

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
theorem HasCompactSupport.contractionProductTest {η : E → ℂ} {ψ : G → ℂ}
    (hη : HasCompactSupport η) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (contractionProductTest η ψ) := by
  apply (hη.prod hψ).of_isClosed_subset isClosed_closure
  exact tsupport_contractionProductTest_subset η ψ

theorem ContDiff.contractionProductTest {η : E → ℂ} {ψ : G → ℂ}
    (hη : ContDiff ℝ ∞ η) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (contractionProductTest η ψ) := by
  exact (hη.comp contDiff_fst).mul (hψ.comp contDiff_snd)

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
theorem tsupport_contractionProductTest_subset_prod {Ω : Set E} {Θ : Set G}
    {η : E → ℂ} {ψ : G → ℂ} (hη : tsupport η ⊆ Ω) (hψ : tsupport ψ ⊆ Θ) :
    tsupport (contractionProductTest η ψ) ⊆ Ω ×ˢ Θ :=
  (tsupport_contractionProductTest_subset η ψ).trans (prod_mono hη hψ)

/-- Differentiating a product test in a retained-variable direction differentiates only `η`. -/
theorem fderiv_contractionProductTest_apply (η : E → ℂ) (ψ : G → ℂ)
    (hη : ContDiff ℝ ∞ η) (hψ : ContDiff ℝ ∞ ψ) (x : E) (y : G) (v : E) :
    fderiv ℝ (contractionProductTest η ψ) (x, y) (v, 0) =
      fderiv ℝ η x v * ψ y := by
  have hηd : HasFDerivAt (fun z : E × G => η z.1)
      ((fderiv ℝ η x).comp (ContinuousLinearMap.fst ℝ E G)) (x, y) :=
    ((hη.differentiable (by simp)).differentiableAt.hasFDerivAt.comp (x, y)
      hasFDerivAt_fst)
  have hψd : HasFDerivAt (fun z : E × G => ψ z.2)
      ((fderiv ℝ ψ y).comp (ContinuousLinearMap.snd ℝ E G)) (x, y) :=
    ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp (x, y)
      hasFDerivAt_snd)
  change fderiv ℝ (fun z : E × G => η z.1 * ψ z.2) (x, y) (v, 0) = _
  rw [fderiv_fun_mul hηd.differentiableAt hψd.differentiableAt,
    hηd.fderiv, hψd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change η x * fderiv ℝ ψ y 0 + ψ y * fderiv ℝ η x v = _
  rw [map_zero, mul_zero, zero_add, mul_comm]

end LiebThirring.TFProduct

end
