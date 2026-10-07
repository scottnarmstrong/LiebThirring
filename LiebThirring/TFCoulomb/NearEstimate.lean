/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.CoulombEnergy
public import LiebThirring.ThomasFermi.Mass
import LiebThirring.TFFunctional.DensityBasic
import LiebThirring.Assembly.CutoffRadial

/-! # The near part of the Thomas–Fermi Coulomb integral

Hölder with exponents 5/3 and 5/2 and the exact radial integral give the
explicit near estimate used in the boxwise Coulomb comparison (and TF finiteness estimates).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring.TFCoulomb

/-- The Coulomb kernel restricted to distances strictly below `s`. -/
@[expose] noncomputable def nearCoulombKernel (s : ℝ) (x y : Position) : ℝ≥0∞ :=
  if ‖x - y‖ < s then coulombKernel x y else 0

theorem measurable_nearCoulombKernel (s : ℝ) :
    Measurable (Function.uncurry (nearCoulombKernel s)) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_fst.sub measurable_snd).norm measurable_const
  · exact (measurable_fst.sub measurable_snd).norm.ennreal_ofReal.inv
  · exact measurable_const

theorem measurable_nearCoulombKernel_right (s : ℝ) (x : Position) :
    Measurable (nearCoulombKernel s x) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_const.sub measurable_id).norm measurable_const
  · exact (measurable_const.sub measurable_id).norm.ennreal_ofReal.inv
  · exact measurable_const

/-- Exact integral of the conjugate power of the near Coulomb kernel. -/
theorem lintegral_near_coulombKernel_rpow (s : ℝ) (hs : 0 < s) (x : Position) :
    (∫⁻ y, nearCoulombKernel s x y ^ ((5 : ℝ) / 2)) =
      ENNReal.ofReal (8 * Real.pi * Real.sqrt s) := by
  have heq (y : Position) : nearCoulombKernel s x y = Assembly.nucleusCutoff 1 s x y := by
    simp only [nearCoulombKernel, coulombKernel, Assembly.nucleusCutoff,
      norm_sub_rev x y, ENNReal.ofReal_one, one_mul]
  simp_rw [heq]
  simpa only [Real.one_rpow, mul_one] using
    Assembly.lintegral_nucleusCutoff_rpow 1 s zero_le_one hs x

/-- The 5/2 norm of the cutoff kernel, with the source's explicit constant. -/
theorem near_coulombKernel_rpow_norm (s : ℝ) (hs : 0 < s) (x : Position) :
    (∫⁻ y, nearCoulombKernel s x y ^ ((5 : ℝ) / 2)) ^ (1 / ((5 : ℝ) / 2)) =
      ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) := by
  rw [lintegral_near_coulombKernel_rpow s hs x,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg s), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hs.le]
  norm_num

/-- Uniform one-center near-potential bound for every Thomas–Fermi density. -/
theorem lintegral_near_coulombKernel_tfDensity_le (ρ : TFDensity)
    (s : ℝ) (hs : 0 < s) (x : Position) :
    (∫⁻ y, nearCoulombKernel s x y ∂tfDensityMeasure ρ) ≤
      ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) *
        eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume := by
  have hm := Lp.aestronglyMeasurable ρ.val
  rw [tfDensityMeasure, lintegral_withDensity_eq_lintegral_mul₀
    hm.aemeasurable.ennreal_ofReal (measurable_nearCoulombKernel_right s x).aemeasurable]
  have hc : (5 / 3 : ℝ).HolderConjugate (5 / 2 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hc
    hm.aemeasurable.ennreal_ofReal (measurable_nearCoulombKernel_right s x).aemeasurable
  have hnorm : (∫⁻ y : Position, ENNReal.ofReal (ρ.val y) ^ ((5 : ℝ) / 3)) ^
      (1 / ((5 : ℝ) / 3)) =
      eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
      (ENNReal.div_ne_top (by norm_num) (by norm_num)) hm]
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ρ.property.1] with y hy
    rw [Real.enorm_eq_ofReal hy]
  rw [hnorm, near_coulombKernel_rpow_norm s hs x] at h
  exact h.trans_eq (mul_comm _ _)

/-- The extended double-integral near estimate, before the TF factor one half. -/
theorem lintegral_near_coulombEnergy_tfDensity_le (ρ : TFDensity)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ∫⁻ y, nearCoulombKernel s x y ∂tfDensityMeasure ρ ∂tfDensityMeasure ρ) ≤
      ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) *
        eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume *
          ENNReal.ofReal (tfMass ρ) := by
  calc
    _ ≤ ∫⁻ _x : Position,
        ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) *
          eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume
        ∂tfDensityMeasure ρ :=
      lintegral_mono (lintegral_near_coulombKernel_tfDensity_le ρ s hs)
    _ = _ := by rw [lintegral_const, TFFunctional.tfDensityMeasure_univ]

/-- The near double integral is finite on the literal TF carrier. -/
theorem lintegral_near_coulombEnergy_tfDensity_lt_top (ρ : TFDensity)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ∫⁻ y, nearCoulombKernel s x y ∂tfDensityMeasure ρ ∂tfDensityMeasure ρ) < ⊤ := by
  apply lt_of_le_of_lt (lintegral_near_coulombEnergy_tfDensity_le ρ s hs)
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp ρ.val).eLpNorm_lt_top)
    ENNReal.ofReal_lt_top

/-- The near part of `D(ρ,ρ)`, including the TF factor one half. -/
theorem half_near_coulombEnergy_tfDensity_le (ρ : TFDensity)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ x, ∫⁻ y, nearCoulombKernel s x y ∂tfDensityMeasure ρ ∂tfDensityMeasure ρ).toReal / 2 ≤
      ((8 * Real.pi) ^ ((2 : ℝ) / 5) / 2) * tfMass ρ *
        (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal *
          s ^ ((1 : ℝ) / 5) := by
  have h := lintegral_near_coulombEnergy_tfDensity_le ρ s hs
  have ht : ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) *
      eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume *
        ENNReal.ofReal (tfMass ρ) ≠ ⊤ :=
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp ρ.val).eLpNorm_lt_top)
      ENNReal.ofReal_lt_top).ne
  have hr := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hs.le _)),
    ENNReal.toReal_ofReal (TFFunctional.tfMass_nonneg ρ)] at hr
  calc
    _ ≤ (((8 * Real.pi) ^ ((2 : ℝ) / 5) * s ^ ((1 : ℝ) / 5)) *
        (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal *
          tfMass ρ) / 2 := div_le_div_of_nonneg_right hr (by norm_num)
    _ = _ := by ring

end LiebThirring.TFCoulomb

end
