/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.FirstVariationPairing
public import LiebThirring.TFMinimizer.AnnulusDensity

/-! # Holder control of the TF kinetic first variation

The exponents 5/2 and 5/3 show that kinetic pairing with an
annulus indicator grows as its volume to the power 3/5, slower than its
Coulomb cavity potential under a three-dimensional dilation.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem integral_kinetic_pair_le (ρ σ : TFDensity) :
    (∫ x : Position, (ρ.val x) ^ ((2 : ℝ) / 3) * σ.val x) ≤
      (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((2 : ℝ) / 5) *
        (∫ x : Position, (σ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) := by
  have hg : MemLp (fun x : Position => σ.val x) (ENNReal.ofReal ((5 : ℝ) / 3)) volume := by
    convert Lp.memLp σ.val using 1
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      ((5 : ℝ) / 2).HolderConjugate ((5 : ℝ) / 3))
    (show 0 ≤ᵐ[volume] (fun x : Position => (ρ.val x) ^ ((2 : ℝ) / 3)) from
      (tfDensity_ae_nonneg ρ).mono (fun _ hx => Real.rpow_nonneg hx _))
    (tfDensity_ae_nonneg σ) (memLp_tfDensity_rpow_two_thirds ρ) hg
  have he : (∫ x : Position, ((ρ.val x) ^ ((2 : ℝ) / 3)) ^ ((5 : ℝ) / 2)) =
      ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) := by
    apply integral_congr_ae
    filter_upwards [tfDensity_ae_nonneg ρ] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  rw [he] at h
  norm_num only [one_div_div] at h
  exact h

theorem integral_kinetic_tfAnnulusDensity (L : ℝ) :
    (∫ x : Position, ((tfAnnulusDensity L).val x) ^ ((5 : ℝ) / 3)) =
      tfMass (tfAnnulusDensity L) := by
  unfold tfMass
  apply integral_congr_ae
  filter_upwards [tfAnnulusDensity_apply_ae L] with x hx
  rw [hx]
  by_cases hxs : x ∈ tfAnnulus L <;>
    simp [hxs, Real.zero_rpow (by norm_num : (5 : ℝ) / 3 ≠ 0)]

end LiebThirring.TFMinimizer

end
