/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.ScalarWeakMultiplier
public import LiebThirring.Sobolev.LipschitzIntegrationByParts

/-! # The scalar weak derivative of a real Lipschitz function -/

public section

open MeasureTheory
open scoped ContDiff NNReal

namespace LiebThirring.Sobolev

private theorem scalar_part_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℂ →L[ℝ] ℝ) (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun y => ℓ (φ y)) x v = ℓ (fderiv ℝ φ x v) := by
  have h := ℓ.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt
  exact congrArg (fun f : E →L[ℝ] ℝ => f v) h.fderiv

/-- The measurable classical derivative supplied by Rademacher is the distributional
derivative of a real Lipschitz function, also for complex scalar test functions. -/
theorem hasScalarWeakDerivative_lipschitz {N : ℕ} (a : Fin N × Fin 3)
    (b : Configuration N → ℝ) (C : ℝ≥0) (hb : LipschitzWith C b) :
    HasScalarWeakDerivative a (fun x => (b x : ℂ))
      (fun x => (lipschitzDirectionalDerivative b a x : ℂ)) := by
  intro φ hφK hφ
  let db := lipschitzDirectionalDerivative b a
  let dφ := fun x => fderiv ℝ φ x (coordinateVector a)
  have hi₀ : Integrable (fun x => (db x : ℂ) * φ x) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφK).bdd_mul
      (Complex.measurable_ofReal.comp (lipschitzDirectionalDerivative_measurable b a)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Complex.norm_real] using norm_lipschitzDirectionalDerivative_le b C hb a x))
  have hi₁ : Integrable (fun x => (b x : ℂ) * dφ x) := by
    have hc : Continuous (fun x => (b x : ℂ) * dφ x) :=
      (Complex.continuous_ofReal.comp hb.continuous).mul
        ((hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const))
    exact hc.integrable_of_hasCompactSupport
      ((hφK.fderiv_apply ℝ _).mul_left (f := fun x => (b x : ℂ)))
  have hpart (ℓ : ℂ →L[ℝ] ℝ) :
      ℓ (∫ x, (db x : ℂ) * φ x) = -ℓ (∫ x, (b x : ℂ) * dφ x) := by
    rw [← ℓ.integral_comp_comm hi₀, ← ℓ.integral_comp_comm hi₁]
    have hs := integral_mul_coordinateDerivative_eq_neg_of_lipschitz a b
      (fun x => ℓ (φ x)) C hb (ℓ.contDiff.comp hφ)
      (hφK.comp_left (map_zero ℓ))
    simp_rw [scalar_part_fderiv ℓ φ hφ] at hs
    have he (r : ℝ) (z : ℂ) : ℓ ((r : ℂ) * z) = r * ℓ z := by
      have hz : (r : ℂ) * z = r • z := by rfl
      rw [hz, map_smul, smul_eq_mul]
    simp_rw [he]
    exact (neg_eq_iff_eq_neg.mpr hs).symm
  apply Complex.ext
  · simpa only [Complex.reCLM_apply, Complex.neg_re] using hpart Complex.reCLM
  · simpa only [Complex.imCLM_apply, Complex.neg_im] using hpart Complex.imCLM

end LiebThirring.Sobolev

end
