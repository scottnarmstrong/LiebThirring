/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Radialization
import LiebThirring.Screening.Rotations
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Radial disintegration

A finite measure invariant under the orientation-preserving rotations about a
center is the mixture of uniform sphere probabilities determined by its radii.
The proof averages its characteristic function over a frequency sphere, swaps
the finite integrals, and invokes characteristic function uniqueness.

Radial disintegration step.
-/

public section

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace LiebThirring

private theorem centered_fourier_rotation (c : Position) (μ : Measure Position)
    (Q : Position ≃ₗᵢ[ℝ] Position)
    (hQ : μ.map (fun x => c + Q (x-c)) = μ) (t : Position) :
    (∫ x, Complex.exp ((⟪x-c, Q t⟫ : ℝ) * Complex.I) ∂μ) =
      ∫ x, Complex.exp ((⟪x-c, t⟫ : ℝ) * Complex.I) ∂μ := by
  conv_lhs => rw [← hQ]
  rw [integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rw [add_sub_cancel_left, Q.inner_map_map]

private theorem sphere_fourier_rotation (Q : Position ≃ₗᵢ[ℝ] Position) (t : Position) :
    (∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪(ω : Position), Q t⟫ : ℝ) * Complex.I) ∂unitSphereMeasure) =
    ∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪(ω : Position), t⟫ : ℝ) * Complex.I) ∂unitSphereMeasure := by
  conv_lhs => rw [← map_unitSphereMeasure_rotation Q]
  rw [integral_map (measurable_unitSphereRotation Q).aemeasurable (by fun_prop)]
  congr 1
  funext ω
  exact congrArg (fun z : ℝ => Complex.exp (z * Complex.I)) (Q.inner_map_map ω t)

private theorem sphere_fourier_norm_eq {s t : Position} (h : ‖s‖ = ‖t‖) :
    (∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪(ω : Position), s⟫ : ℝ) * Complex.I) ∂unitSphereMeasure) =
    ∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪(ω : Position), t⟫ : ℝ) * Complex.I) ∂unitSphereMeasure := by
  obtain ⟨Q, hQ, _⟩ := exists_rotation_map_eq_of_norm_eq h
  rw [← hQ]
  exact (sphere_fourier_rotation Q s).symm

private theorem sphere_fourier_norm_swap (x t : Position) :
    (∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪x, ‖t‖ • (ω : Position)⟫ : ℝ) * Complex.I) ∂unitSphereMeasure) =
    ∫ ω : Metric.sphere (0 : Position) 1,
      Complex.exp ((⟪‖x‖ • (ω : Position), t⟫ : ℝ) * Complex.I) ∂unitSphereMeasure := by
  simp_rw [inner_smul_right, real_inner_smul_left]
  have h : ‖‖t‖ • x‖ = ‖‖x‖ • t‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_norm, mul_comm]
  convert sphere_fourier_norm_eq h using 1 <;> congr 1 <;> funext ω
  · rw [inner_smul_right, real_inner_comm]
  · rw [inner_smul_right]

private theorem centered_fourier_norm_eq (c : Position) (μ : Measure Position)
    (hμ : IsRadial c μ) {s t : Position} (h : ‖s‖ = ‖t‖) :
    (∫ x, Complex.exp ((⟪x-c, s⟫ : ℝ) * Complex.I) ∂μ) =
      ∫ x, Complex.exp ((⟪x-c, t⟫ : ℝ) * Complex.I) ∂μ := by
  obtain ⟨Q, hQ, hdet⟩ := exists_rotation_map_eq_of_norm_eq h
  rw [← hQ]
  exact (centered_fourier_rotation c μ Q (hμ Q hdet) s).symm

private theorem centered_fourier_radialize (c t : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] (hμ : IsRadial c μ) :
    (∫ x, Complex.exp ((⟪x-c, t⟫ : ℝ) * Complex.I) ∂μ) =
      ∫ x, Complex.exp ((⟪x-c, t⟫ : ℝ) * Complex.I) ∂radialize c μ := by
  have hnorm (ω : Metric.sphere (0 : Position) 1) : ‖‖t‖ • (ω : Position)‖ = ‖t‖ := by
    have hω : ‖(ω : Position)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using ω.property
    rw [norm_smul, Real.norm_eq_abs, abs_norm, hω, mul_one]
  have hi : Integrable (fun p : Position × Metric.sphere (0 : Position) 1 =>
      Complex.exp ((⟪p.1-c, ‖t‖ • (p.2 : Position)⟫ : ℝ) * Complex.I))
      (μ.prod unitSphereMeasure) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  have hj : Integrable (fun p : Position × Metric.sphere (0 : Position) 1 =>
      Complex.exp ((⟪‖p.1-c‖ • (p.2 : Position), t⟫ : ℝ) * Complex.I))
      (μ.prod unitSphereMeasure) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
  calc
    _ = ∫ ω : Metric.sphere (0 : Position) 1, (∫ x,
        Complex.exp ((⟪x-c, ‖t‖ • (ω : Position)⟫ : ℝ) * Complex.I) ∂μ) ∂unitSphereMeasure := by
      have heq (ω : Metric.sphere (0 : Position) 1) :=
        centered_fourier_norm_eq c μ hμ (hnorm ω)
      simp_rw [heq]
      simp only [integral_const, probReal_univ, one_smul]
    _ = ∫ x, (∫ ω : Metric.sphere (0 : Position) 1,
        Complex.exp ((⟪x-c, ‖t‖ • (ω : Position)⟫ : ℝ) * Complex.I) ∂unitSphereMeasure) ∂μ :=
      (integral_integral_swap hi).symm
    _ = ∫ x, (∫ ω : Metric.sphere (0 : Position) 1,
        Complex.exp ((⟪‖x-c‖ • (ω : Position), t⟫ : ℝ) * Complex.I) ∂unitSphereMeasure) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => sphere_fourier_norm_swap (x-c) t)
    _ = _ := by
      rw [radialize_eq_map_prod, integral_map (by fun_prop) (by fun_prop)]
      simp only [add_sub_cancel_left]
      exact (integral_prod _ hj).symm

theorem radialize_eq_self_of_isRadial (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] (hμ : IsRadial c μ) : radialize c μ = μ := by
  have hmap : μ.map (fun x => x-c) = (radialize c μ).map (fun x => x-c) := by
    apply Measure.ext_of_charFun
    funext t
    simp only [charFun_apply]
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
    exact centered_fourier_radialize c t μ hμ
  have hback := congrArg (fun ν : Measure Position => ν.map (fun x => x+c)) hmap
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hback
  simp only [Function.comp_def, sub_add_cancel] at hback
  change μ.map id = (radialize c μ).map id at hback
  simpa only [Measure.map_id] using hback.symm

end LiebThirring
end
