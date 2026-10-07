/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.UniformCoercivity
public import LiebThirring.TFFunctional.NearMinimizers

/-! # Continuity in the Thomas--Fermi kinetic coefficient -/

public section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

/-- An explicit kinetic bound for unit-accuracy near minimizers on a compact
positive coefficient interval. -/
@[expose] noncomputable def coefficientLipschitzConstant {M : ℕ}
    (amin : ℝ) (amax : {a : ℝ // 0 < a}) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : ℝ :=
  (2 / amin) *
    (tfFunctional amax z R (tfBallDensity ν 0 ⟨1, zero_lt_one⟩) +
      uniformTFCoercivityConstant amin ν z + 1)

theorem coefficientLipschitzConstant_pos {M : ℕ} {amin : ℝ} (hamin : 0 < amin)
    (amax : {a : ℝ // 0 < a}) (hmax : amin ≤ amax.val) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    0 < coefficientLipschitzConstant amin amax ν z R := by
  have hmass := tfMass_tfBallDensity ν 0 ⟨1, zero_lt_one⟩
  have hlo := tfFunctional_coercive_lower_bound_uniform amax hamin hmax ν z R
    (tfBallDensity ν 0 ⟨1, zero_lt_one⟩) hmass.le
  have hK := integral_tfDensity_rpow_five_thirds_nonneg
    (tfBallDensity ν 0 ⟨1, zero_lt_one⟩)
  have hkin : 0 ≤ amax.val / 2 *
      (∫ x : Position, ((tfBallDensity ν 0 ⟨1, zero_lt_one⟩).val x) ^
        ((5 : ℝ) / 3)) := mul_nonneg (div_nonneg amax.property.le (by norm_num)) hK
  unfold coefficientLipschitzConstant
  have hsum : 0 ≤ tfFunctional amax z R (tfBallDensity ν 0 ⟨1, zero_lt_one⟩) +
      uniformTFCoercivityConstant amin ν z := by
    linarith only [hlo, hkin]
  exact mul_pos (div_pos (by norm_num) hamin) (lt_add_of_le_of_pos hsum zero_lt_one)

private theorem near_minimizer_kinetic_le {M : ℕ}
    (a : {a : ℝ // 0 < a}) {amin : ℝ} (hamin : 0 < amin) (hmina : amin ≤ a.val)
    (amax : {a : ℝ // 0 < a}) (hamax : a.val ≤ amax.val)
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hmass : tfMass ρ = (ν : ℝ))
    (hnear : tfFunctional a z R ρ < (tfEnergy a ν z R).toReal + 1) :
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) <
      coefficientLipschitzConstant amin amax ν z R := by
  let trial := tfBallDensity ν 0 ⟨1, zero_lt_one⟩
  have htrialMass : tfMass trial = (ν : ℝ) := tfMass_tfBallDensity ν 0 ⟨1, zero_lt_one⟩
  have hEa := tfEnergy_toReal_le_trial a ν z R trial htrialMass
  have hmono : tfFunctional a z R trial ≤ tfFunctional amax z R trial := by
    rw [← sub_nonneg]
    rw [tfFunctional_sub_tfFunctional]
    exact mul_nonneg (sub_nonneg.mpr hamax)
      (integral_tfDensity_rpow_five_thirds_nonneg trial)
  have hlo := tfFunctional_coercive_lower_bound_uniform a hamin hmina ν z R ρ hmass.le
  have hcoef : amin / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ≤
      a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) :=
    mul_le_mul_of_nonneg_right (by linarith) (integral_tfDensity_rpow_five_thirds_nonneg ρ)
  have hmain : amin / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) <
      tfFunctional amax z R trial + uniformTFCoercivityConstant amin ν z + 1 := by
    linarith only [hnear, hEa, hmono, hlo, hcoef]
  unfold coefficientLipschitzConstant
  rw [show (2 / amin) *
      (tfFunctional amax z R trial + uniformTFCoercivityConstant amin ν z + 1) =
      (tfFunctional amax z R trial + uniformTFCoercivityConstant amin ν z + 1) /
        (amin / 2) by field_simp]
  apply (lt_div_iff₀ (half_pos hamin)).2
  calc
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) * (amin / 2) =
        amin / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) := mul_comm _ _
    _ < _ := hmain

private theorem tfEnergy_toReal_sub_le {M : ℕ}
    {amin : ℝ} (hamin : 0 < amin) (amax : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (a b : {a : ℝ // 0 < a})
    (hb : amin ≤ b.val ∧ b.val ≤ amax.val) :
    (tfEnergy a ν z R).toReal - (tfEnergy b ν z R).toReal ≤
      coefficientLipschitzConstant amin amax ν z R * |a.val - b.val| := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  obtain ⟨ρ, hm, hnear⟩ := exists_tfDensity_near_tfEnergy b ν z R δ hδ
  have htrial := tfEnergy_toReal_le_trial a ν z R ρ hm
  have hnearOne : tfFunctional b z R ρ < (tfEnergy b ν z R).toReal + 1 :=
    hnear.trans_le (by dsimp [δ]; exact add_le_add_right (min_le_right ε 1) _)
  have hnearEps : tfFunctional b z R ρ < (tfEnergy b ν z R).toReal + ε :=
    hnear.trans_le (by dsimp [δ]; exact add_le_add_right (min_le_left ε 1) _)
  have hK := near_minimizer_kinetic_le b hamin hb.1 amax hb.2 ν z R ρ hm hnearOne
  have hdiff := tfFunctional_sub_tfFunctional a b z R ρ
  have hmul : (a.val - b.val) * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ≤
      |a.val - b.val| * coefficientLipschitzConstant amin amax ν z R := by
    calc
      _ ≤ |a.val - b.val| * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (integral_tfDensity_rpow_five_thirds_nonneg ρ)
      _ ≤ _ := mul_le_mul_of_nonneg_left hK.le (abs_nonneg _)
  linarith only [hnearEps, htrial, hdiff, hmul]

theorem tfEnergy_toReal_lipschitzOn_Icc {M : ℕ}
    {amin : ℝ} (hamin : 0 < amin) (amax : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (a b : {a : ℝ // 0 < a})
    (ha : amin ≤ a.val ∧ a.val ≤ amax.val)
    (hb : amin ≤ b.val ∧ b.val ≤ amax.val) :
    |(tfEnergy a ν z R).toReal - (tfEnergy b ν z R).toReal| ≤
      coefficientLipschitzConstant amin amax ν z R * |a.val - b.val| := by
  have hab := tfEnergy_toReal_sub_le hamin amax ν z R a b hb
  have hba := tfEnergy_toReal_sub_le hamin amax ν z R b a ha
  rw [abs_sub_comm] at hba
  rw [abs_le]
  constructor <;> linarith only [hab, hba]

/-- The actual exact-mass TF infimum is continuous in its positive kinetic
coefficient. -/
theorem continuousAt_tfEnergy_toReal {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) :
    ContinuousAt (fun b : {b : ℝ // 0 < b} => (tfEnergy b ν z R).toReal) a := by
  let amin : ℝ := a.val / 2
  let amax : {b : ℝ // 0 < b} :=
    ⟨3 * a.val / 2, div_pos (mul_pos (by norm_num) a.property) (by norm_num)⟩
  let B := coefficientLipschitzConstant amin amax ν z R
  have hamin : 0 < amin := half_pos a.property
  have hamax : amin ≤ amax.val := by dsimp [amin, amax]; linarith [a.property]
  have hB : 0 < B := coefficientLipschitzConstant_pos hamin amax hamax ν z R
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min amin (ε / (B + 1)), lt_min hamin (div_pos hε (by linarith)), ?_⟩
  intro b hb
  have habs : |b.val - a.val| < min amin (ε / (B + 1)) := by
    simpa only [Real.dist_eq, Subtype.dist_eq] using hb
  have habsA : |b.val - a.val| < amin := habs.trans_le (min_le_left _ _)
  have habsE : |b.val - a.val| < ε / (B + 1) := habs.trans_le (min_le_right _ _)
  have hbounds : amin ≤ b.val ∧ b.val ≤ amax.val := by
    have h := abs_lt.mp habsA
    dsimp [amin, amax] at h ⊢
    constructor <;> linarith [a.property]
  have habounds : amin ≤ a.val ∧ a.val ≤ amax.val := by
    dsimp [amin, amax]
    constructor <;> linarith [a.property]
  have henergy := tfEnergy_toReal_lipschitzOn_Icc hamin amax ν z R b a hbounds habounds
  have hfrac : B * (ε / (B + 1)) < ε := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < B + 1)).2
    nlinarith only [hε]
  rw [Real.dist_eq]
  calc
    _ ≤ B * |b.val - a.val| := henergy
    _ < B * (ε / (B + 1)) := mul_lt_mul_of_pos_left habsE hB
    _ < ε := hfrac

end LiebThirring.TFFunctional

end
