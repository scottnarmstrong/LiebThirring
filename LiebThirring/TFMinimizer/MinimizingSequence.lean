/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.Convexity
public import LiebThirring.TFFunctional.NearMinimizers
public import LiebThirring.TFFunctional.MassCompletion

/-! # Strong Cauchy TF minimizing sequences

Coercivity and the midpoint defect control the actual
near-minimizers of the literal infimum.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem tfRelaxedEnergy_toReal_le_trial {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hcap : tfMass ρ ≤ (ν : ℝ)) :
    (tfRelaxedEnergy a ν z R).toReal ≤ tfFunctional a z R ρ := by
  have hf := tfEnergy_ne_top_ne_bot_library a ν z R
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hf.2.2.1 hf.2.2.2]
  exact tfRelaxedEnergy_le_trial a ν z R ρ hcap

/-- Uniform norm bound for an energy sublevel under the mass cap. -/
theorem exists_norm_bound_of_tfFunctional_le {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) (E : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) →
      tfFunctional a z R ρ ≤ E → ‖ρ.val‖ ≤ B := by
  let L := (|E| + tfCoercivityConstant a ν z + 1) / (a.val / 2)
  have hcoer := tfCoercivityConstant_nonneg a ν z
  have hL : 0 < L := div_pos (by linarith [abs_nonneg E]) (half_pos a.property)
  refine ⟨L ^ ((3 : ℝ) / 5) + 1, by positivity, ?_⟩
  intro ρ hcap hE
  have hk : ‖ρ.val‖ ^ ((5 : ℝ) / 3) ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ (half_pos a.property)).mpr
    have h := tfFunctional_coercive_lower_bound a ν z R ρ hcap
    rw [integral_tfDensity_rpow_eq_norm] at h
    nlinarith only [h, hE, le_abs_self E]
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg ρ.val) _) hk
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [← Real.rpow_mul (norm_nonneg ρ.val)] at h
  norm_num at h
  linarith

/-- Actual competitors converge in energy to the relaxed infimum, with a
uniform upper bound from the first term onward. -/
theorem exists_tfRelaxed_minimizing_sequence {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∃ f : ℕ → TFDensity,
      (∀ j, tfMass (f j) ≤ (ν : ℝ)) ∧
      (∀ j, tfFunctional a z R (f j) ≤ (tfRelaxedEnergy a ν z R).toReal + 1) ∧
      Tendsto (fun j => tfFunctional a z R (f j)) atTop
        (𝓝 (tfRelaxedEnergy a ν z R).toReal) := by
  have hpos : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) := fun j => by positivity
  choose f hmass hnear using fun j : ℕ => exists_tfDensity_near_tfEnergy a ν z R
    (1 / ((j : ℝ) + 1)) (hpos j)
  have heq := tfEnergy_eq_tfRelaxedEnergy_library a ν z R
  rw [heq] at hnear
  have hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ) := fun j => (hmass j).le
  refine ⟨f, hcap, ?_, ?_⟩
  · intro j
    have hε : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) j]
    linarith [hnear j]
  · have hsub : Tendsto (fun j => tfFunctional a z R (f j) -
        (tfRelaxedEnergy a ν z R).toReal) atTop (𝓝 0) :=
      squeeze_zero (fun j => sub_nonneg.mpr (tfRelaxedEnergy_toReal_le_trial a ν z R (f j) (hcap j)))
        (fun j => by linarith [hnear j])
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [sub_add_cancel, zero_add] using hsub.add_const
      (tfRelaxedEnergy a ν z R).toReal

/-- Quantitative convexity makes every bounded-norm minimizing sequence
strong Cauchy in the original L5/3 carrier. -/
theorem cauchySeq_of_tfRelaxed_minimizing {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (f : ℕ → TFDensity) (hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ))
    (hF : Tendsto (fun j => tfFunctional a z R (f j)) atTop
      (𝓝 (tfRelaxedEnergy a ν z R).toReal))
    (B : ℝ) (hB : 0 < B) (hbound : ∀ j, ‖(f j).val‖ ≤ B) :
    CauchySeq (fun j => (f j).val) := by
  let c := (5 / 36 : ℝ) * a.val / (2 * B) ^ ((1 : ℝ) / 3)
  have hc : 0 < c := div_pos (mul_pos (by norm_num) a.property)
    (Real.rpow_pos_of_pos (by positivity) _)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsmall : ∀ᶠ j in atTop, tfFunctional a z R (f j) <
      (tfRelaxedEnergy a ν z R).toReal + c * ε ^ 2 :=
    hF.eventually (eventually_lt_nhds (lt_add_of_pos_right _ (mul_pos hc (sq_pos_of_pos hε))))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hsmall
  refine ⟨J, fun j hj k hk => ?_⟩
  have hmid : tfMass (tfMidpoint (f j) (f k)) ≤ (ν : ℝ) := by
    rw [tfMass_tfMidpoint]
    linarith [hcap j, hcap k]
  have hlo := tfRelaxedEnergy_toReal_le_trial a ν z R _ hmid
  have hq := tfFunctional_midpoint_defect_controls_norm a z R B hB (f j) (f k)
    (hbound j) (hbound k)
  change c * ‖(f j).val - (f k).val‖ ^ 2 ≤ _ at hq
  rw [dist_eq_norm]
  have hsq : ‖(f j).val - (f k).val‖ ^ 2 < ε ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left hc).mp
    linarith [hJ j hj, hJ k hk]
  nlinarith [norm_nonneg ((f j).val - (f k).val)]

end LiebThirring.TFMinimizer

end
