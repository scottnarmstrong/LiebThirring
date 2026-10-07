/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedPositivity

/-!
# Complex Hilbert-valued weighted positivity

The real part is taken after the complex integrals, as in the weighted positivity.
No finite-dimensional target hypothesis is needed at the smooth level.
-/

public section
open MeasureTheory
namespace LiebThirring
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The individual complex kinetic cross terms are integrable. -/
theorem integrable_ionization_complex_cross {ε : ℝ} (hε : 0 ≤ ε) {f : Position → H}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (i : Fin 3) :
    Integrable (fun x => inner ℂ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i))) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let e := EuclideanSpace.basisFun (Fin 3) ℝ i
  let d := fun x => fderiv ℝ f x e
  have hdc : Continuous d := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdsc : HasCompactSupport d := hfc.fderiv_apply ℝ e
  have hw : LocallyIntegrable (fun x : Position => ionizationWeight ε ‖x‖) :=
    (lipschitzWith_ionizationWeight hε).continuous.locallyIntegrable
  have h₁ : Integrable (fun x => ionizationWeight ε ‖x‖ • inner ℂ (d x) (d x)) := by
    apply hw.integrable_smul_right_of_hasCompactSupport (hdc.inner hdc)
    apply hdsc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    rw [hx, inner_zero_left]
  have h₂ : Integrable (fun x => (ionizationGradCoeff ε ‖x‖ * inner ℝ x e) •
      inner ℂ (f x) (d x)) := by
    apply (locallyIntegrable_ionizationGrad hε i).integrable_smul_right_of_hasCompactSupport
      (hf.continuous.inner hdc)
    apply hfc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    rw [hx, inner_zero_left]
  apply (h₁.add h₂).congr
  filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
  rw [fderiv_ionizationWeight_smul hε (hf.differentiable (by norm_num)) hx, inner_add_left]
  have hs (r : ℝ) (u v : H) : inner ℂ (r • u) v = r • inner ℂ u v := by
    change inner ℂ ((r : ℂ) • u) v = r • inner ℂ u v
    exact inner_smul_real_left (𝕜 := ℂ) u v r
  rw [hs, hs]
  rfl

/-- Weighted positivity for smooth Hilbert-valued functions. -/
theorem integral_ionization_complex_cross_nonneg {ε : ℝ} (hε : 0 ≤ ε) {f : Position → H}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (∑ i : Fin 3, ∫ x, inner ℂ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i))).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [Complex.re_sum]
  have he (i : Fin 3) : (∫ x, inner ℂ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i))).re =
      ∫ x, inner ℝ (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)) :=
    (integral_re (integrable_ionization_complex_cross hε hf hfc i)).symm
  simp_rw [he]
  exact integral_ionization_cross_nonneg hε hf hfc

end LiebThirring
end
