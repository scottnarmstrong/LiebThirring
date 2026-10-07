/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Dilation
public import LiebThirring.ThomasFermi.Functional

/-! # Scaling of the local Thomas--Fermi terms -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

theorem integral_rpow_tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 < A)
    (ρ : TFDensity) :
    (∫ x : Position, ((tfDensityDilation β A hβ hA.le ρ).val x) ^ ((5 : ℝ) / 3)) =
      A ^ ((5 : ℝ) / 3) * (β ^ 3)⁻¹ *
        ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) := by
  calc
    _ = ∫ x : Position, (A * ρ.val (β • x)) ^ ((5 : ℝ) / 3) := by
      apply integral_congr_ae
      filter_upwards [tfDensityDilation_coe_ae β A hβ hA.le ρ] with x hx
      rw [hx]
      simp only [tfDensityDilationFn]
    _ = A ^ ((5 : ℝ) / 3) *
        ∫ x : Position, (ρ.val (β • x)) ^ ((5 : ℝ) / 3) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_smul
        (volume : Measure Position) hβ.ne').ae ρ.property.1] with x hρ
      rw [Real.mul_rpow hA.le hρ]
    _ = _ := by
      have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Position)
        (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3)) β (hR := hβ.le)
      simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at h
      rw [h]
      ring

theorem tfNuclearPotential_dilation {M : ℕ} (β : ℝ) (Z : ℝ≥0) (hβ : 0 < β)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) :
    tfNuclearPotential (fun k => Z * z k)
      (fun k => β⁻¹ • R k) x =
      (Z : ℝ) * β * tfNuclearPotential z R (β • x) := by
  unfold tfNuclearPotential
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hb : β ≠ 0 := hβ.ne'
  have hv : x - β⁻¹ • R k = β⁻¹ • (β • x - R k) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [NNReal.coe_mul, hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hβ.le),
    div_eq_mul_inv, mul_inv, inv_inv]
  ring

theorem integral_tfNuclearPotential_mul_tfDensityDilation {M : ℕ}
    (β A : ℝ) (Z : ℝ≥0) (hβ : 0 < β) (hA : 0 ≤ A)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) :
    (∫ x : Position, tfNuclearPotential (fun k => Z * z k)
        (fun k => β⁻¹ • R k) x * (tfDensityDilation β A hβ hA ρ).val x) =
      (Z : ℝ) * β * A * (β ^ 3)⁻¹ *
        ∫ x : Position, tfNuclearPotential z R x * ρ.val x := by
  calc
    _ = ∫ x : Position, ((Z : ℝ) * β * A) *
        (tfNuclearPotential z R (β • x) * ρ.val (β • x)) := by
      apply integral_congr_ae
      filter_upwards [tfDensityDilation_coe_ae β A hβ hA ρ] with x hx
      rw [tfNuclearPotential_dilation β Z hβ z R x, hx]
      simp only [tfDensityDilationFn]
      ring
    _ = ((Z : ℝ) * β * A) *
        ∫ x : Position, tfNuclearPotential z R (β • x) * ρ.val (β • x) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [Measure.integral_comp_smul_of_nonneg (volume : Measure Position)
        (fun x : Position => tfNuclearPotential z R x * ρ.val x) β (hR := hβ.le)]
      simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
      ring

end LiebThirring

end
