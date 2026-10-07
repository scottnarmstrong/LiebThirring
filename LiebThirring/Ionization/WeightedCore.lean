/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedSmoothIntegration

/-!
# Radial weighted positivity on the compact smooth core

The vector-field square identity, the weighted Hardy inequality, and the
kinetic cross-form identity in the weighted positivity. The main square identity applies also at nonzero values at the origin,
using a.e. coordinate lines. No Fourier/H¹
extension is asserted in this module.
-/

public section
open MeasureTheory
open scoped RealInnerProductSpace
namespace LiebThirring
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Exact expansion of the square for `A(x) = x / |x|²`, away from the origin. -/
theorem ionization_square_pointwise {ε : ℝ} {x : Position} (hx : x ≠ 0)
    (u : F) (g : Fin 3 → F) :
    (∑ i : Fin 3, ionizationWeight ε ‖x‖ * ‖g i + (x i / ‖x‖ ^ 2) • u‖ ^ 2) =
      ionizationWeight ε ‖x‖ * (∑ i : Fin 3, ‖g i‖ ^ 2) +
      2 * (∑ i : Fin 3, (ionizationFieldCoeff ε ‖x‖ * x i) * inner ℝ u (g i)) +
      ionizationFieldCoeff ε ‖x‖ * ‖u‖ ^ 2 := by
  simp_rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, mul_add]
  simp_rw [real_inner_comm u]
  simp only [Finset.sum_add_distrib]
  have hcross (i : Fin 3) :
      ionizationWeight ε ‖x‖ * (2 * (x i / ‖x‖ ^ 2 * inner ℝ u (g i))) =
        2 * ((ionizationFieldCoeff ε ‖x‖ * x i) * inner ℝ u (g i)) := by
    dsimp [ionizationWeight, ionizationFieldCoeff]
    field_simp [norm_ne_zero_iff.mpr hx]
  have hmass : (∑ i : Fin 3,
      ionizationWeight ε ‖x‖ * ((x i / ‖x‖ ^ 2) ^ 2 * ‖u‖ ^ 2)) =
      ionizationFieldCoeff ε ‖x‖ * ‖u‖ ^ 2 := by
    simp_rw [div_pow]
    rw [show (∑ i : Fin 3, ionizationWeight ε ‖x‖ *
      ((x i ^ 2 / (‖x‖ ^ 2) ^ 2) * ‖u‖ ^ 2)) =
        (ionizationWeight ε ‖x‖ / ‖x‖ ^ 4 * ‖u‖ ^ 2) * ∑ i : Fin 3, x i ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [← EuclideanSpace.real_norm_sq_eq]
    dsimp [ionizationWeight, ionizationFieldCoeff]
    field_simp [norm_ne_zero_iff.mpr hx]
  simp_rw [hcross]
  rw [hmass, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The weighted Hardy square identity on the compact smooth core. -/
theorem integral_ionization_square {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, ∑ i : Fin 3, ionizationWeight ε ‖x‖ *
      ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i) +
        (x i / ‖x‖ ^ 2) • f x‖ ^ 2) =
      (∫ x, ionizationWeight ε ‖x‖ * ∑ i : Fin 3,
        ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) -
      ∫ x, ionizationGradCoeff ε ‖x‖ * ‖f x‖ ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let b := fun i (x : Position) => ionizationFieldCoeff ε ‖x‖ * inner ℝ x (e i)
  have hb := fun (i : Fin 3) (x : Position) (hx : x ≠ 0) => contDiffAt_ionizationField hε hx (e i)
  have hlb := fun i => locallyIntegrable_ionizationField hε i
  have hw : LocallyIntegrable (fun x : Position => ionizationWeight ε ‖x‖) :=
    (lipschitzWith_ionizationWeight hε).continuous.locallyIntegrable
  have hm : Integrable (fun x => ionizationGradCoeff ε ‖x‖ * ‖f x‖ ^ 2) :=
    integrable_smooth_weight_norm_sq hf hfc (locallyIntegrable_ionization_kernel hε 2)
  have hn : Integrable (fun x => ionizationFieldCoeff ε ‖x‖ * ‖f x‖ ^ 2) := by
    simpa only [ionizationFieldCoeff, pow_one] using
      integrable_smooth_weight_norm_sq hf hfc (locallyIntegrable_ionization_kernel hε 1)
  have hg := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_smooth_weight_deriv_sq hf hfc hw (e i))
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_smooth_weight_inner hf hfc (hlb i) (e i))
  have hdiv := integral_smooth_divergence_norm_sq hf hfc b
    (fun i x hx => (hb i x hx).differentiableAt one_ne_zero) hlb
    (fun i => locallyIntegrable_fderiv_ionizationField hε i)
  have hdiv' : (∫ x, ionizationGradCoeff ε ‖x‖ * ‖f x‖ ^ 2) +
      (∫ x, ionizationFieldCoeff ε ‖x‖ * ‖f x‖ ^ 2) =
      -2 * ∑ i : Fin 3, ∫ x, b i x * inner ℝ (f x) (fderiv ℝ f x (e i)) := by
    rw [← integral_add hm hn]
    rw [← hdiv]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    rw [show (∑ i, fderiv ℝ (b i) x (e i)) =
      ionizationGradCoeff ε ‖x‖ + ionizationFieldCoeff ε ‖x‖ from sum_fderiv_ionizationField hε hx]
    ring
  have hs : (∫ x, ∑ i : Fin 3, ionizationWeight ε ‖x‖ *
      ‖fderiv ℝ f x (e i) + (x i / ‖x‖ ^ 2) • f x‖ ^ 2) =
      (∫ x, ∑ i : Fin 3, ionizationWeight ε ‖x‖ * ‖fderiv ℝ f x (e i)‖ ^ 2) +
      2 * (∫ x, ∑ i : Fin 3, b i x * inner ℝ (f x) (fderiv ℝ f x (e i))) +
      ∫ x, ionizationFieldCoeff ε ‖x‖ * ‖f x‖ ^ 2 := by
    have hsplit := integral_add (hg.add (hi.const_mul 2)) hn
    simp only [Pi.add_apply, integral_add hg (hi.const_mul 2), integral_const_mul] at hsplit
    rw [← hsplit]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    simp only [e, EuclideanSpace.inner_basisFun_real, ← Finset.mul_sum]
    simpa only [← Finset.mul_sum] using
      (ionization_square_pointwise (ε := ε) hx (f x) (fun i => fderiv ℝ f x (e i)))
  rw [integral_finsetSum _ (fun i _ =>
    integrable_smooth_weight_inner hf hfc (hlb i) (e i))] at hs
  simp only [← Finset.mul_sum] at hs ⊢
  dsimp only [e, b] at hs hdiv'
  linarith only [hs, hdiv']

/-- The first, stronger inequality in the weighted positivity on the smooth core. -/
theorem integral_ionization_hardy_le {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, ionizationGradCoeff ε ‖x‖ * ‖f x‖ ^ 2) ≤
      ∫ x, ionizationWeight ε ‖x‖ * ∑ i : Fin 3,
        ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 := by
  have hp : 0 ≤ ∫ x : Position, ∑ i : Fin 3, ionizationWeight ε ‖x‖ *
      ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i) + (x i / ‖x‖ ^ 2) • f x‖ ^ 2 :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (ionizationWeight_nonneg hε (norm_nonneg x)) (sq_nonneg _)))
  rw [integral_ionization_square hε hf hfc] at hp
  exact sub_nonneg.mp hp

end LiebThirring
end
