/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.InfimumComparison
public import LiebThirring.TFFunctional.AttractionCoercivity
public import LiebThirring.TFCore.CutoffComparison
import LiebThirring.TFFunctional.CoefficientContinuity

/-! # Cutoff infima and the ordered small parameters of the molecular limit

The regular potential gives an infimum above the honest TF infimum.
Coefficient continuity selects η; the proved core estimate then selects
δ. Both choices precede the large-charge threshold.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFLimit

/-- The kinetic coefficient retained after reserving ηT for nuclear cores. -/
@[expose] noncomputable def reducedKineticCoefficient
    (q : {q : ℕ // 1 ≤ q}) (η : ℝ) (hη : η < 1) : {a : ℝ // 0 < a} :=
  ⟨(1 - η) * (tfKineticConstant q).val,
    mul_pos (sub_pos.mpr hη) (tfKineticConstant q).property⟩

theorem tfFunctional_le_regularTFFunctional {M : ℕ}
    (a : {a : ℝ // 0 < a}) (δ : ℝ) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) :
    tfFunctional a z R ρ ≤ TFCoulomb.regularTFFunctional a.val δ z R ρ := by
  have hV : (∫ x : Position, tfCappedNuclearPotential δ z R x * ρ.val x) ≤
      ∫ x : Position, tfNuclearPotential z R x * ρ.val x := by
    apply integral_mono_ae
      (TFCoulomb.integrable_tfCappedNuclearPotential_mul_tfDensity hδ z R ρ)
      (TFFunctional.integrable_tfNuclearPotential_mul z R ρ)
    filter_upwards [TFCore.capped_nuclearPotential_le_ae δ z R,
      TFFunctional.tfDensity_ae_nonneg ρ] with x hx hρ
    exact mul_le_mul_of_nonneg_right hx hρ
  unfold tfFunctional TFCoulomb.regularTFFunctional
  linarith only [hV]

/-- The cutoff comparison is proved on the actual infima, after finiteness. -/
theorem tfEnergy_toReal_le_regularTFInfimum {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (tfEnergy a ν z R).toReal ≤ TFCoulomb.regularTFInfimum a.val (ν : ℝ) δ z R := by
  have hf := TFFunctional.tfEnergy_ne_top_ne_bot_library a ν z R
  apply le_csInf (TFCoulomb.regularTFValues_nonempty a.val δ ν z R)
  rintro E ⟨ρ, hm, rfl⟩
  have htf : tfEnergy a ν z R ≤ (tfFunctional a z R ρ : EReal) := by
    unfold tfEnergy
    exact iInf_le (fun σ : {σ : TFDensity // tfMass σ = (ν : ℝ)} =>
      (tfFunctional a z R σ.val : EReal)) ⟨ρ, hm⟩
  have hreal := EReal.toReal_le_toReal htf hf.2.1 (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at hreal
  exact hreal.trans (tfFunctional_le_regularTFFunctional a δ hδ z R ρ)

/-- Coefficient continuity supplies the first small parameter η. -/
theorem exists_kinetic_fraction_close {M : ℕ}
    (q : {q : ℕ // 1 ≤ q}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, ∃ hη : η < 1, 0 < η ∧
      |(tfEnergy (reducedKineticCoefficient q η hη) ν z R).toReal -
        (tfEnergy (tfKineticConstant q) ν z R).toReal| < ε := by
  have hcontinuity :=
    TFFunctional.continuousAt_tfEnergy_toReal (tfKineticConstant q) ν z R
  obtain ⟨d, hd, hclose⟩ := Metric.continuousAt_iff.mp hcontinuity ε hε
  let K := (tfKineticConstant q).val
  have hK : 0 < K := (tfKineticConstant q).property
  let η := min (d / (2 * K)) (1 / 2)
  have hη : 0 < η := lt_min (div_pos hd (mul_pos (by norm_num) hK)) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨η, hη1, hη, ?_⟩
  have hdist : dist (reducedKineticCoefficient q η hη1) (tfKineticConstant q) < d := by
    change |(1 - η) * K - K| < d
    rw [show (1 - η) * K - K = -(η * K) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hη.le hK.le)]
    calc
      η * K ≤ (d / (2 * K)) * K :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hK.le
      _ = d / 2 := by field_simp
      _ < d := half_lt_self hd
  have h := hclose hdist
  simpa only [Real.dist_eq] using h

/-- After fixing η, choose a positive cutoff radius with arbitrarily small core error. -/
theorem exists_core_radius_error_lt (q : ℕ) {M : ℕ} (z : Fin M → ℝ≥0)
    (η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, TFCore.coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ < ε := by
  let c := TFCore.coreErrorConstant q z * η ^ (-(3 : ℝ) / 2)
  have hc : 0 ≤ c := mul_nonneg (TFCore.coreErrorConstant_nonneg q z) (Real.rpow_nonneg hη.le _)
  let d := ε / (2 * (c + 1))
  have hd : 0 < d := div_pos hε (mul_pos (by norm_num) (by linarith only [hc]))
  refine ⟨d ^ 2, sq_pos_of_pos hd, ?_⟩
  rw [Real.sqrt_sq hd.le]
  change c * d < ε
  calc
    c * d ≤ (c + 1) * d := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hd.le
    _ = ε / 2 := by dsimp only [d]; field_simp
    _ < ε := half_lt_self hε

end LiebThirring.TFLimit
end
