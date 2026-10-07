/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.BoxEnergy
public import LiebThirring.TFCoulomb.CoulombFinite
import LiebThirring.TFFunctional.DensityBasic

/-! # Uniform continuum comparison for the box Coulomb form

Near error `(8π)^(2/5) ν B₀ s^(1/5)/2` and far error
`√3 ν² ℓ/s²`. The stronger estimate here requires only positive `ℓ,s`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring.TFCoulomb

theorem tfBoxCoulombEnergy_nonneg (ℓ : ℝ) (ρ : TFDensity) :
    0 ≤ tfBoxCoulombEnergy ℓ ρ := ENNReal.toReal_nonneg

theorem tfBoxCoulombEnergy_le {ℓ : ℝ} (hℓ : 0 < ℓ) (ρ : TFDensity) :
    tfBoxCoulombEnergy ℓ ρ ≤ tfCoulombEnergy ρ ρ := by
  have h := ENNReal.toReal_mono
    (ENNReal.div_ne_top (tf_coulombEnergy_ne_top ρ) (by norm_num))
    (boxCoulombEnergy_le hℓ (tfDensityMeasure ρ))
  simpa only [tfBoxCoulombEnergy, tfCoulombEnergy, ENNReal.toReal_div,
    ENNReal.toReal_ofNat] using h

/-- Integral kernel comparison, before converting finite energies to real values. -/
theorem coulombEnergy_le_box_integral_add {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (μ : Measure Position) [SFinite μ] :
    coulombEnergy μ μ ≤
      (∫⁻ x, ∫⁻ y, boxCoulombKernel ℓ x y ∂μ ∂μ) +
      (∫⁻ x, ∫⁻ y, nearCoulombKernel s x y ∂μ ∂μ) +
      ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) * μ Set.univ * μ Set.univ := by
  rw [coulombEnergy_eq_lintegral]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, boxCoulombKernel ℓ x y + nearCoulombKernel s x y +
        ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) ∂μ ∂μ :=
      lintegral_mono fun x => lintegral_mono (coulombKernel_le_box_add_near hℓ hs x)
    _ = _ := by
      have hsplit (x : Position) :
          (∫⁻ y, boxCoulombKernel ℓ x y + nearCoulombKernel s x y +
            ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) ∂μ) =
          (∫⁻ y, boxCoulombKernel ℓ x y ∂μ) +
          (∫⁻ y, nearCoulombKernel s x y ∂μ) +
            ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) * μ Set.univ := by
        have hm : Measurable (fun y => boxCoulombKernel ℓ x y + nearCoulombKernel s x y) :=
          (measurable_boxCoulombKernel_right hℓ x).add (measurable_nearCoulombKernel_right s x)
        rw [lintegral_add_left hm,
          lintegral_add_left (measurable_boxCoulombKernel_right hℓ x), lintegral_const]
      simp_rw [hsplit]
      have hb : Measurable (fun x => ∫⁻ y, boxCoulombKernel ℓ x y ∂μ) :=
        (measurable_boxCoulombKernel hℓ).lintegral_prod_right
      have hn : Measurable (fun x => ∫⁻ y, nearCoulombKernel s x y ∂μ) :=
        (measurable_nearCoulombKernel s).lintegral_prod_right
      have hm : Measurable (fun x => (∫⁻ y, boxCoulombKernel ℓ x y ∂μ) +
          (∫⁻ y, nearCoulombKernel s x y ∂μ)) := hb.add hn
      rw [lintegral_add_left hm, lintegral_add_left hb, lintegral_const]

/-- Explicit error for every TF density; no analytic estimate is assumed. -/
theorem tfCoulombEnergy_sub_tfBoxCoulombEnergy_le {ℓ s : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (ρ : TFDensity) :
    tfCoulombEnergy ρ ρ - tfBoxCoulombEnergy ℓ ρ ≤
      ((8 * Real.pi) ^ ((2 : ℝ) / 5) / 2) * tfMass ρ *
        (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal *
          s ^ ((1 : ℝ) / 5) + Real.sqrt 3 * tfMass ρ ^ 2 * ℓ / s ^ 2 := by
  let μ := tfDensityMeasure ρ
  let : IsFiniteMeasure μ := isFiniteMeasure_tfDensityMeasure ρ
  let Ib := ∫⁻ x, ∫⁻ y, boxCoulombKernel ℓ x y ∂μ ∂μ
  let In := ∫⁻ x, ∫⁻ y, nearCoulombKernel s x y ∂μ ∂μ
  let c := ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) * μ Set.univ * μ Set.univ
  have hb : Ib ≠ ⊤ := by
    apply ne_top_of_le_ne_top (tf_coulombEnergy_ne_top ρ)
    unfold Ib μ
    rw [coulombEnergy_eq_lintegral]
    exact lintegral_mono fun x => lintegral_mono (boxCoulombKernel_le hℓ x)
  have hn : In ≠ ⊤ := (lintegral_near_coulombEnergy_tfDensity_lt_top ρ s hs).ne
  have hc : c ≠ ⊤ := by
    unfold c μ
    rw [TFFunctional.tfDensityMeasure_univ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨hb, hn⟩, hc⟩)
    (coulombEnergy_le_box_integral_add hℓ hs μ)
  change (coulombEnergy μ μ).toReal ≤ (Ib + In + c).toReal at h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hb, hn⟩) hc,
    ENNReal.toReal_add hb hn] at h
  have hbox : tfBoxCoulombEnergy ℓ ρ = Ib.toReal / 2 := by
    rw [tfBoxCoulombEnergy, boxCoulombEnergy_eq_lintegral hℓ,
      ENNReal.toReal_div, ENNReal.toReal_ofNat]
  have hconst : c.toReal / 2 = Real.sqrt 3 * tfMass ρ ^ 2 * ℓ / s ^ 2 := by
    unfold c μ
    rw [TFFunctional.tfDensityMeasure_univ, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (TFFunctional.tfMass_nonneg ρ)]
    ring
  have hnear := half_near_coulombEnergy_tfDensity_le ρ s hs
  change In.toReal / 2 ≤ _ at hnear
  rw [hbox, ← hconst]
  unfold tfCoulombEnergy
  change (coulombEnergy μ μ).toReal / 2 - Ib.toReal / 2 ≤ _
  linarith only [h, hnear]

/-- The boxwise Coulomb comparison is uniform on the specified mass and L^(5/3) ball. -/
theorem tfCoulombEnergy_sub_tfBoxCoulombEnergy_bounds {ℓ s ν B₀ : ℝ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (ρ : TFDensity)
    (hm : tfMass ρ ≤ ν)
    (hn : (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal ≤ B₀) :
    0 ≤ tfCoulombEnergy ρ ρ - tfBoxCoulombEnergy ℓ ρ ∧
      tfCoulombEnergy ρ ρ - tfBoxCoulombEnergy ℓ ρ ≤
        ((8 * Real.pi) ^ ((2 : ℝ) / 5) / 2) * ν * B₀ * s ^ ((1 : ℝ) / 5) +
          Real.sqrt 3 * ν ^ 2 * ℓ / s ^ 2 := by
  constructor
  · exact sub_nonneg.mpr (tfBoxCoulombEnergy_le hℓ ρ)
  · apply (tfCoulombEnergy_sub_tfBoxCoulombEnergy_le hℓ hs ρ).trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
      apply mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hn
        ENNReal.toReal_nonneg
          (mul_nonneg (by positivity) ((TFFunctional.tfMass_nonneg ρ).trans hm))
    · apply div_le_div_of_nonneg_right _ (sq_nonneg s)
      apply mul_le_mul_of_nonneg_right _ hℓ.le
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
      exact pow_le_pow_left₀ (TFFunctional.tfMass_nonneg ρ) hm 2

/-- Uniform convergence as the mesh tends to zero, with the radius chosen
before the mesh and independently of the competing density. -/
theorem tfBoxCoulombEnergy_uniform {ν B₀ : ℝ} (hν : 0 ≤ ν) (hB : 0 ≤ B₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ ℓ : ℝ, 0 < ℓ → ℓ < η → ∀ ρ : TFDensity,
      tfMass ρ ≤ ν →
      (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal ≤ B₀ →
      0 ≤ tfCoulombEnergy ρ ρ - tfBoxCoulombEnergy ℓ ρ ∧
        tfCoulombEnergy ρ ρ - tfBoxCoulombEnergy ℓ ρ < ε := by
  let A := ((8 * Real.pi) ^ ((2 : ℝ) / 5) / 2) * ν * B₀
  let B := Real.sqrt 3 * ν ^ 2
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) hν) hB
  have hB' : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg 3) (sq_nonneg ν)
  have hcont : ContinuousAt (fun s : ℝ => A * s ^ ((1 : ℝ) / 5)) 0 :=
    continuous_const.continuousAt.mul
      (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 5) (Or.inr (by norm_num)))
  obtain ⟨r, hr, hsmall⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (half_pos hε)
  let s := r / 2
  have hs : 0 < s := half_pos hr
  have hnear : A * s ^ ((1 : ℝ) / 5) < ε / 2 := by
    have h := hsmall (x := s) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs]
      exact half_lt_self hr)
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 5 ≠ 0), mul_zero,
      Real.dist_eq, sub_zero] at h
    rw [abs_of_nonneg (mul_nonneg hA (Real.rpow_nonneg hs.le _))] at h
    exact h
  let η := (ε / 2) * s ^ 2 / (B + 1)
  have hη : 0 < η := div_pos (mul_pos (half_pos hε) (sq_pos_of_pos hs)) (by linarith)
  refine ⟨η, hη, fun ℓ hℓ hmesh ρ hm hn => ?_⟩
  obtain ⟨hlo, hup⟩ := tfCoulombEnergy_sub_tfBoxCoulombEnergy_bounds hℓ hs ρ hm hn
  refine ⟨hlo, hup.trans_lt ?_⟩
  have hfar : B * ℓ / s ^ 2 < ε / 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hs)).mpr
    have hbound : (B + 1) * ℓ < (ε / 2) * s ^ 2 := by
      have h := (lt_div_iff₀ (by linarith : 0 < B + 1)).mp hmesh
      simpa only [mul_comm] using h
    have hm' : B * ℓ ≤ (B + 1) * ℓ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hℓ.le
    exact hm'.trans_lt hbound
  change A * s ^ ((1 : ℝ) / 5) + B * ℓ / s ^ 2 < ε
  linarith only [hnear, hfar]

end LiebThirring.TFCoulomb

end
