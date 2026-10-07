/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.HilbertField

/-! # Tensoring a fixed scalar L² function -/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFProduct

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_fieldTensor (μ : Measure X) (f : Lp ℂ 2 μ) (v : H) :
    ‖fieldTensor μ f v‖ = ‖f‖ * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖fieldTensor μ f v‖ ^ 2 = Complex.re (inner ℂ (fieldTensor μ f v) (fieldTensor μ f v)) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = Complex.re (inner ℂ f f * inner ℂ v v) := by
      rw [inner_fieldTensor_fieldTensor]
    _ = (‖f‖ * ‖v‖) ^ 2 := by
      have hfre := inner_self_eq_norm_sq (𝕜 := ℂ) f
      have hfim := inner_self_im (𝕜 := ℂ) f
      have hvre := inner_self_eq_norm_sq (𝕜 := ℂ) v
      have hvim := inner_self_im (𝕜 := ℂ) v
      simp only [RCLike.re_eq_complex_re] at hfre hvre
      simp only [RCLike.im_eq_complex_im] at hfim hvim
      rw [Complex.mul_re, hfre, hfim, hvre, hvim, mul_zero, sub_zero, mul_pow]

/-- Tensoring a fixed scalar L² function is a bounded linear map in the Hilbert-space factor. -/
noncomputable def fieldTensorRightCLM (μ : Measure X) (f : Lp ℂ 2 μ) :
    H →L[ℂ] Lp H 2 μ :=
  LinearMap.mkContinuous {
    toFun := fieldTensor μ f
    map_add' := by
      intro v w
      apply Lp.ext
      filter_upwards [fieldTensor_ae μ f (v + w), fieldTensor_ae μ f v,
        fieldTensor_ae μ f w, Lp.coeFn_add (fieldTensor μ f v) (fieldTensor μ f w)]
        with x hvw hv hw hadd
      rw [hvw, hadd]
      simp only [Pi.add_apply]
      rw [hv, hw, smul_add]
    map_smul' := by
      intro c v
      apply Lp.ext
      filter_upwards [fieldTensor_ae μ f (c • v), fieldTensor_ae μ f v,
        Lp.coeFn_smul c (fieldTensor μ f v)] with x hcv hv hs
      change fieldTensor μ f (c • v) x = (c • fieldTensor μ f v) x
      rw [hcv, hs]
      simp only [Pi.smul_apply]
      rw [hv, smul_smul]
      simpa only [smul_smul] using
        congrArg (fun z : ℂ => z • v) (mul_comm (f x) c) } ‖f‖ (fun v => by
        change ‖fieldTensor μ f v‖ ≤ ‖f‖ * ‖v‖
        rw [norm_fieldTensor])

end LiebThirring.TFProduct

end
