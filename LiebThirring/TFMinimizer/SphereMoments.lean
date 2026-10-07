/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Electrostatics.Sphere

/-! # First and second moments of normalized spherical measure

Elementary Euclidean identities used by the shell mean-value maximum argument
in the neutrality and saturation. The second moment gains exactly the square of the radius.
-/

public section

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LiebThirring.TFMinimizer

theorem integrable_inner_unitSphere (a : Position) :
    Integrable (fun ω : sphere (0 : Position) 1 => inner ℝ a (ω : Position))
      unitSphereMeasure := by
  apply Integrable.of_bound (by fun_prop) ‖a‖
  filter_upwards [] with ω
  have hω : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [hω, mul_one] using norm_inner_le_norm a (ω : Position)

theorem integral_inner_unitSphere (a : Position) :
    (∫ ω : sphere (0 : Position) 1, inner ℝ a (ω : Position) ∂unitSphereMeasure) = 0 := by
  let Q : Position ≃ₗᵢ[ℝ] Position := LinearIsometryEquiv.neg ℝ
  have he := map_unitSphereMeasure_rotation Q
  have hi : (∫ ω : sphere (0 : Position) 1, inner ℝ a (ω : Position) ∂unitSphereMeasure) =
      -(∫ ω : sphere (0 : Position) 1, inner ℝ a (ω : Position) ∂unitSphereMeasure) := by
    conv_lhs => rw [← he]
    rw [integral_map (measurable_unitSphereRotation Q).aemeasurable (by fun_prop)]
    have hp : (fun ω : sphere (0 : Position) 1 => inner ℝ a (unitSphereRotation Q ω : Position)) =
        fun ω : sphere (0 : Position) 1 => -(inner ℝ a (ω : Position)) := by
      funext ω
      change inner ℝ a (-(ω : Position)) = _
      rw [inner_neg_right]
    rw [hp, integral_neg]
  linarith only [hi]

theorem integral_norm_sq_shell (a : Position) (r : ℝ) (hr : 0 ≤ r) :
    (∫ x : Position, ‖x‖ ^ 2 ∂shell a r) = ‖a‖ ^ 2 + r ^ 2 := by
  rw [shell, integral_map (measurable_shellMap a r).aemeasurable (by fun_prop)]
  have hp : (fun ω : sphere (0 : Position) 1 => ‖a + r • (ω : Position)‖ ^ 2) =
      fun ω : sphere (0 : Position) 1 => (‖a‖ ^ 2 + r ^ 2) +
        (2 * r) * inner ℝ a (ω : Position) := by
    funext ω
    have hω : ‖(ω : Position)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
      hω, mul_one, inner_smul_right]
    ring
  rw [hp, integral_add (integrable_const _) ((integrable_inner_unitSphere a).const_mul _),
    integral_const_mul, integral_inner_unitSphere]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]

end LiebThirring.TFMinimizer

end
