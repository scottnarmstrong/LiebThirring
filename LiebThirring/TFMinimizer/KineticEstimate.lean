/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.ScalarConvexity
public import LiebThirring.TFFunctional.DensityDifference

/-! # Integrated quantitative convexity of the kinetic term

The weighted Hölder step of the quantitative convexity (direct proof).
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem kinetic_weight_le_rpow_sum (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u - v) ^ 2 / (u + v) ^ ((1 : ℝ) / 3) ≤ (u + v) ^ ((5 : ℝ) / 3) := by
  by_cases hs : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    simp [hu0, hv0, Real.zero_rpow (by norm_num : (5 : ℝ) / 3 ≠ 0)]
  have hp : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm hs)
  calc
    _ ≤ (u + v) ^ 2 / (u + v) ^ ((1 : ℝ) / 3) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hp.le _)
      nlinarith [mul_nonneg hu hv]
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_sub hp]
      norm_num

theorem kinetic_weight_holder_factor (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u - v) ^ 2 / (u + v) ^ ((1 : ℝ) / 3)) ^ ((5 : ℝ) / 6) *
        (u + v) ^ ((5 : ℝ) / 18) = |u - v| ^ ((5 : ℝ) / 3) := by
  by_cases hs : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    simp [hu0, hv0, Real.zero_rpow (by norm_num : (5 : ℝ) / 3 ≠ 0)]
  have hp : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm hs)
  rw [Real.div_rpow (sq_nonneg _) (Real.rpow_nonneg hp.le _),
    ← Real.rpow_mul hp.le]
  norm_num
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hp _).ne']
  rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
  norm_num

/-- The weighted quotient controlling the L5/3 difference. -/
@[expose] noncomputable def kineticWeight (ρ σ : TFDensity) (x : Position) : ℝ :=
  (ρ.val x - σ.val x) ^ 2 / (ρ.val x + σ.val x) ^ ((1 : ℝ) / 3)

theorem kineticWeight_ae_nonneg (ρ σ : TFDensity) :
    0 ≤ᵐ[volume] kineticWeight ρ σ := by
  filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ] with x hρ hσ
  exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (add_nonneg hρ hσ) _)

theorem integrable_kineticWeight (ρ σ : TFDensity) :
    Integrable (kineticWeight ρ σ) volume := by
  have hm : AEStronglyMeasurable (kineticWeight ρ σ) volume := by
    unfold kineticWeight
    exact ((((Lp.aestronglyMeasurable ρ.val).sub
      (Lp.aestronglyMeasurable σ.val)).pow 2).aemeasurable.div
      (((Lp.aestronglyMeasurable ρ.val).add
        (Lp.aestronglyMeasurable σ.val)).aemeasurable.pow_const _)).aestronglyMeasurable
  apply (integrable_tfDensity_rpow_five_thirds (tfDensityAdd ρ σ)).mono' hm
  filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ,
    tfDensityAdd_coeFn ρ σ, kineticWeight_ae_nonneg ρ σ] with x hρ hσ ha hw
  rw [Real.norm_of_nonneg hw, ha]
  exact kinetic_weight_le_rpow_sum _ _ hρ hσ

theorem norm_sub_sq_le_integral_kineticWeight (ρ σ : TFDensity) :
    ‖ρ.val - σ.val‖ ^ 2 ≤
      (∫ x : Position, kineticWeight ρ σ x) * ‖ρ.val + σ.val‖ ^ ((1 : ℝ) / 3) := by
  let w := kineticWeight ρ σ
  let s := fun x : Position => (tfDensityAdd ρ σ).val x
  have hw := kineticWeight_ae_nonneg ρ σ
  have hs := tfDensity_ae_nonneg (tfDensityAdd ρ σ)
  have hf : MemLp (fun x => w x ^ ((5 : ℝ) / 6)) (ENNReal.ofReal ((6 : ℝ) / 5)) volume := by
    have h := (memLp_one_iff_integrable.mpr (integrable_kineticWeight ρ σ)).norm_rpow_div
      ((5 : ℝ≥0∞) / 6)
    norm_num [ENNReal.toReal_div] at h
    apply (memLp_congr_ae (show (fun x => ‖w x‖ ^ ((5 : ℝ) / 6)) =ᵐ[volume]
        (fun x => w x ^ ((5 : ℝ) / 6)) from ?_)).mp
      (by
        convert h using 1
        apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr (by norm_num))).mp
        norm_num [ENNReal.toReal_div, ENNReal.toReal_inv])
    filter_upwards [hw] with x hx
    rw [Real.norm_of_nonneg hx]
  have hg : MemLp (fun x => s x ^ ((5 : ℝ) / 18)) (ENNReal.ofReal (6 : ℝ)) volume := by
    have h := (Lp.memLp (tfDensityAdd ρ σ).val).norm_rpow_div ((5 : ℝ≥0∞) / 18)
    norm_num [ENNReal.toReal_div] at h
    apply (memLp_congr_ae (show (fun x => ‖s x‖ ^ ((5 : ℝ) / 18)) =ᵐ[volume]
        (fun x => s x ^ ((5 : ℝ) / 18)) from ?_)).mp
      (by
        convert h using 1
        apply (ENNReal.toReal_eq_toReal_iff' (by norm_num)
          (ENNReal.div_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
            (by norm_num))).mp
        norm_num [ENNReal.toReal_div])
    filter_upwards [hs] with x hx
    rw [Real.norm_of_nonneg hx]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show ((6 : ℝ) / 5).HolderConjugate 6 by
      apply Real.holderConjugate_iff.mpr; norm_num)
    (show 0 ≤ᵐ[volume] (fun x => w x ^ ((5 : ℝ) / 6)) by
      filter_upwards [hw] with x hx; exact Real.rpow_nonneg hx _)
    (show 0 ≤ᵐ[volume] (fun x => s x ^ ((5 : ℝ) / 18)) by
      filter_upwards [hs] with x hx; exact Real.rpow_nonneg hx _) hf hg
  have heq : (∫ x : Position, w x ^ ((5 : ℝ) / 6) * s x ^ ((5 : ℝ) / 18)) =
      ‖ρ.val - σ.val‖ ^ ((5 : ℝ) / 3) := by
    rw [← norm_tfDensityAbsDiff, ← integral_tfDensity_rpow_eq_norm]
    apply integral_congr_ae
    filter_upwards [tfDensity_ae_nonneg ρ, tfDensity_ae_nonneg σ,
      tfDensityAdd_coeFn ρ σ, tfDensityAbsDiff_apply_ae ρ σ] with x hρ hσ ha hd
    dsimp [w, s, kineticWeight]
    rw [ha, hd]
    exact kinetic_weight_holder_factor _ _ hρ hσ
  have heqf : (∫ x : Position, (w x ^ ((5 : ℝ) / 6)) ^ ((6 : ℝ) / 5)) =
      ∫ x : Position, w x := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
    rfl
  have heqg : (∫ x : Position, (s x ^ ((5 : ℝ) / 18)) ^ (6 : ℝ)) =
      ‖ρ.val + σ.val‖ ^ ((5 : ℝ) / 3) := by
    change _ = ‖(tfDensityAdd ρ σ).val‖ ^ ((5 : ℝ) / 3)
    rw [← integral_tfDensity_rpow_eq_norm]
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  rw [heq, heqf, heqg] at h
  have hi : 0 ≤ ∫ x : Position, w x := integral_nonneg_of_ae hw
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h
    (by norm_num : (0 : ℝ) ≤ 6 / 5)
  rw [Real.mul_rpow (Real.rpow_nonneg hi _) (Real.rpow_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) _),
    ← Real.rpow_mul (norm_nonneg (ρ.val - σ.val)),
    ← Real.rpow_mul hi, ← Real.rpow_mul (norm_nonneg (ρ.val + σ.val)),
    ← Real.rpow_mul (norm_nonneg (ρ.val + σ.val))] at hp
  norm_num at hp
  exact hp

end LiebThirring.TFMinimizer

end
