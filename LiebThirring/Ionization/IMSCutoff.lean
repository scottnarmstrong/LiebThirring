/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSLipschitz
public import LiebThirring.Ionization.IMSSectors

/-! # The explicit radial IMS cutoff

This is the piecewise-linear angle prescribed in the IMS partition, represented by a clamp.
-/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring
open Sobolev

/-- The angle `0`, `(π/2)(t-1)`, `π/2` on the three cutoff regions. -/
@[expose] noncomputable def imsAngle (t : ℝ) : ℝ :=
  (Real.pi / 2) * max (min (t - 1) 1) 0

theorem imsAngle_of_le_one {t : ℝ} (ht : t ≤ 1) : imsAngle t = 0 := by
  rw [imsAngle]
  have : t - 1 ≤ 0 := sub_nonpos.mpr ht
  rw [min_eq_left (this.trans zero_le_one), max_eq_right this, mul_zero]

theorem imsAngle_of_two_le {t : ℝ} (ht : 2 ≤ t) : imsAngle t = Real.pi / 2 := by
  rw [imsAngle]
  have htop : 1 ≤ t - 1 := by linarith
  rw [min_eq_right htop, max_eq_left zero_le_one, mul_one]

/-- The exact Lipschitz constant of the clamped angle. -/
theorem lipschitzWith_imsAngle :
    LipschitzWith (NNReal.mk (Real.pi / 2) (by positivity)) imsAngle := by
  have hshift : LipschitzWith 1 (fun t : ℝ => t - 1) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using le_rfl
  have hclamp : LipschitzWith 1 (fun t : ℝ => max (min (t - 1) 1) 0) := by
    exact (hshift.min_const 1).max_const 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (imsAngle x) (imsAngle y) ≤ (Real.pi / 2) * dist x y
  rw [Real.dist_eq, imsAngle, imsAngle, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2)]
  have hd := (lipschitzWith_iff_dist_le_mul.mp hclamp) x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hd
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-- Inside cutoff at radius `R`. -/
@[expose] noncomputable def imsChi (R : ℝ) (x : Position) : ℝ :=
  Real.cos (imsAngle (‖x‖ / R))

/-- Outside cutoff at radius `R`. -/
@[expose] noncomputable def imsEta (R : ℝ) (x : Position) : ℝ :=
  Real.sin (imsAngle (‖x‖ / R))

theorem imsChi_sq_add_imsEta_sq (R : ℝ) (x : Position) :
    imsChi R x ^ 2 + imsEta R x ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq _

theorem norm_imsChi_le_one (R : ℝ) (x : Position) : ‖imsChi R x‖ ≤ 1 := by
  simpa [imsChi, Real.norm_eq_abs] using Real.abs_cos_le_one (imsAngle (‖x‖ / R))

theorem norm_imsEta_le_one (R : ℝ) (x : Position) : ‖imsEta R x‖ ≤ 1 := by
  simpa [imsEta, Real.norm_eq_abs] using Real.abs_sin_le_one (imsAngle (‖x‖ / R))

/-- The outside cutoff vanishes on the closed ball of radius `R`. -/
theorem imsEta_eq_zero_of_norm_le {R : ℝ} (hR : 0 < R) {x : Position}
    (hx : ‖x‖ ≤ R) : imsEta R x = 0 := by
  rw [imsEta, imsAngle_of_le_one ((div_le_one hR).mpr hx), Real.sin_zero]

/-- The inside cutoff vanishes outside the closed ball of radius `2R`. -/
theorem imsChi_eq_zero_of_two_mul_le_norm {R : ℝ} (hR : 0 < R) {x : Position}
    (hx : 2 * R ≤ ‖x‖) : imsChi R x = 0 := by
  have htwo : 2 ≤ ‖x‖ / R := (le_div_iff₀ hR).mpr hx
  rw [imsChi, imsAngle_of_two_le htwo, Real.cos_pi_div_two]

/-- The radial angle has Lipschitz constant `π/(2R)` for `R > 0`. -/
theorem lipschitzWith_imsRadialAngle {R : ℝ} (hR : 0 < R) :
    LipschitzWith (NNReal.mk (Real.pi / (2 * R)) (by positivity))
      (fun x : Position => imsAngle (‖x‖ / R)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (imsAngle (‖x‖ / R)) (imsAngle (‖y‖ / R)) ≤
    (Real.pi / (2 * R)) * dist x y
  calc
    dist (imsAngle (‖x‖ / R)) (imsAngle (‖y‖ / R))
        ≤ (Real.pi / 2) * dist (‖x‖ / R) (‖y‖ / R) :=
          (lipschitzWith_iff_dist_le_mul.mp lipschitzWith_imsAngle) _ _
    _ = (Real.pi / (2 * R)) * dist ‖x‖ ‖y‖ := by
      rw [Real.dist_eq, Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hR]
      field_simp
    _ ≤ (Real.pi / (2 * R)) * dist x y := by
      have hd := (lipschitzWith_iff_dist_le_mul.mp lipschitzWith_one_norm) x y
      simp only [NNReal.coe_one, one_mul] at hd
      exact mul_le_mul_of_nonneg_left hd (by positivity)

theorem lipschitzWith_imsChi {R : ℝ} (hR : 0 < R) :
    LipschitzWith (NNReal.mk (Real.pi / (2 * R)) (by positivity)) (imsChi R) := by
  change LipschitzWith _ (Real.cos ∘ fun x : Position => imsAngle (‖x‖ / R))
  simpa only [one_mul] using Real.lipschitzWith_cos.comp (lipschitzWith_imsRadialAngle hR)

theorem lipschitzWith_imsEta {R : ℝ} (hR : 0 < R) :
    LipschitzWith (NNReal.mk (Real.pi / (2 * R)) (by positivity)) (imsEta R) := by
  change LipschitzWith _ (Real.sin ∘ fun x : Position => imsAngle (‖x‖ / R))
  simpa only [one_mul] using Real.lipschitzWith_sin.comp (lipschitzWith_imsRadialAngle hR)

/-- For a Lipschitz angle, the squared derivatives of its sine and cosine pair equal the
squared derivative of the angle at almost every point. -/
theorem ae_sq_lipschitzDirectionalDerivative_cos_add_sin {N : ℕ}
    (φ : Configuration N → ℝ) (C : ℝ≥0) (hφ : LipschitzWith C φ) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ a : Fin N × Fin 3,
      lipschitzDirectionalDerivative (fun y => Real.cos (φ y)) a x ^ 2 +
        lipschitzDirectionalDerivative (fun y => Real.sin (φ y)) a x ^ 2 =
          lipschitzDirectionalDerivative φ a x ^ 2 := by
  filter_upwards [hφ.ae_differentiableAt_configuration] with x hx
  intro a
  have hc := Real.hasDerivAt_cos (φ x) |>.hasFDerivAt.comp x hx.hasFDerivAt
  have hs := Real.hasDerivAt_sin (φ x) |>.hasFDerivAt.comp x hx.hasFDerivAt
  change lipschitzDirectionalDerivative (Real.cos ∘ φ) a x ^ 2 +
      lipschitzDirectionalDerivative (Real.sin ∘ φ) a x ^ 2 =
        lipschitzDirectionalDerivative φ a x ^ 2
  rw [lipschitzDirectionalDerivative, lipschitzDirectionalDerivative,
    lipschitzDirectionalDerivative, hc.fderiv, hs.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  calc
    _ = (fderiv ℝ φ x (coordinateVector a)) ^ 2 *
        (Real.sin (φ x) ^ 2 + Real.cos (φ x) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

end LiebThirring

end
