/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterCoulomb
public import LiebThirring.TFFunctional.FunctionalAlgebra

/-! # Identification of the orbital direct energy with the TF direct energy

All positive extended integrals are identified before conversion to reals.
In particular the two conventions for the factor one half agree exactly.
Lieb–Simon (1977) III.11, p. 66.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFUpper

theorem coulombEnergy_tfDensity_eq_product (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) =
      ∫⁻ p : Position × Position, coulombKernel p.1 p.2 *
        ENNReal.ofReal (ρ.val p.1 * σ.val p.2) := by
  rw [coulombEnergy_eq_lintegral]
  simp only [tfDensityMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul _
    ((Lp.stronglyMeasurable ρ.val).measurable.ennreal_ofReal)
    (measurable_coulombKernel.lintegral_prod_right)]
  simp_rw [lintegral_withDensity_eq_lintegral_mul _
    ((Lp.stronglyMeasurable σ.val).measurable.ennreal_ofReal)
    (measurable_coulombKernel_right _)]
  simp only [Pi.mul_apply]
  change (∫⁻ x : Position, ENNReal.ofReal (ρ.val x) *
    ∫⁻ y : Position, ENNReal.ofReal (σ.val y) * coulombKernel x y) = _
  erw [Measure.volume_eq_prod, lintegral_prod _
    (measurable_coulombKernel.mul
      ((((Lp.stronglyMeasurable ρ.val).measurable.comp measurable_fst).mul
        ((Lp.stronglyMeasurable σ.val).measurable.comp measurable_snd)).ennreal_ofReal)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ρ.property.1] with x hx
  erw [← lintegral_const_mul _
    (((Lp.stronglyMeasurable σ.val).measurable.ennreal_ofReal).mul
      (measurable_coulombKernel_right x))]
  apply lintegral_congr_ae
  filter_upwards [σ.property.1] with y hy
  change ENNReal.ofReal (ρ.val x) * (ENNReal.ofReal (σ.val y) * coulombKernel x y) =
    coulombKernel x y * ENNReal.ofReal (ρ.val x * σ.val y)
  calc
    _ = coulombKernel x y * (ENNReal.ofReal (ρ.val x) * ENNReal.ofReal (σ.val y)) := by
      ring
    _ = _ := congrArg (coulombKernel x y * ·) (ENNReal.ofReal_mul hx).symm

/-- The direct orbital term is the finite positive TF integral. -/
theorem slaterDirectCoulomb_eq_tfDensity {n q : ℕ} (u : Fin n → State 1 q)
    (d : TFDensity) (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x) :
    slaterDirectCoulomb u = (2 : ℝ≥0∞)⁻¹ *
      coulombEnergy (tfDensityMeasure d) (tfDensityMeasure d) := by
  rw [slaterDirectCoulomb, coulombEnergy_tfDensity_eq_product]
  apply congrArg (fun t : ℝ≥0∞ => (2 : ℝ≥0∞)⁻¹ * t)
  apply lintegral_congr_ae
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hd,
    Measure.quasiMeasurePreserving_snd.ae hd] with p hx hy
  exact congrArg (fun t : ℝ => coulombKernel p.1 p.2 * ENNReal.ofReal t)
    (congrArg₂ (· * ·) hx hy).symm

theorem slaterDirectCoulomb_lt_top_of_tfDensity {n q : ℕ}
    (u : Fin n → State 1 q) (d : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x) :
    slaterDirectCoulomb u < ⊤ := by
  rw [slaterDirectCoulomb_eq_tfDensity u d hd]
  exact ENNReal.mul_lt_top (by norm_num) (TFFunctional.coulombEnergy_tfDensity_lt_top d d)

theorem slaterDirectCoulomb_toReal_eq_tfDensity {n q : ℕ}
    (u : Fin n → State 1 q) (d : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x) :
    (slaterDirectCoulomb u).toReal = tfCoulombEnergy d d := by
  rw [slaterDirectCoulomb_eq_tfDensity u d hd, ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  simp only [ENNReal.toReal_ofNat, tfCoulombEnergy]
  ring

theorem tfDensityMeasure_smul (b : ℝ≥0) (d : TFDensity) :
    tfDensityMeasure (TFFunctional.tfDensitySMul b d) =
      (b : ℝ≥0∞) • tfDensityMeasure d := by
  unfold tfDensityMeasure
  calc
    _ = volume.withDensity (fun x => (b : ℝ≥0∞) * ENNReal.ofReal (d.val x)) := by
      apply withDensity_congr_ae
      filter_upwards [TFFunctional.tfDensitySMul_coeFn b d] with x hx
      exact (congrArg ENNReal.ofReal hx).trans
        ((ENNReal.ofReal_mul b.property).trans
          (congrArg (fun t : ℝ≥0∞ => t * ENNReal.ofReal (d.val x))
            (show ENNReal.ofReal (b : ℝ) = (b : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)))
    _ = _ := withDensity_smul _ ((Lp.stronglyMeasurable d.val).measurable.ennreal_ofReal)

theorem tfCoulombEnergy_smul (b : ℝ≥0) (d e : TFDensity) :
    tfCoulombEnergy (TFFunctional.tfDensitySMul b d) (TFFunctional.tfDensitySMul b e) =
      (b : ℝ) ^ 2 * tfCoulombEnergy d e := by
  unfold tfCoulombEnergy
  rw [tfDensityMeasure_smul, tfDensityMeasure_smul,
    TFFunctional.coulombEnergy_smul_left, TFFunctional.coulombEnergy_smul_right]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  ring

theorem integral_nuclearPotential_smul {M : ℕ} (b : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (d : TFDensity) :
    (∫ x : Position, tfNuclearPotential z R x * (TFFunctional.tfDensitySMul b d).val x) =
      (b : ℝ) * ∫ x : Position, tfNuclearPotential z R x * d.val x := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [TFFunctional.tfDensitySMul_coeFn b d] with x hx
  rw [hx]
  ring

end LiebThirring.TFUpper
end
