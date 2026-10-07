/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.PotentialApproximation
public import LiebThirring.TFCoulomb.UniformComparison
import LiebThirring.TFFunctional.DensityBasic
import LiebThirring.TFFunctional.TrialDensities

/-! # The regular discrete TF infimum tends to the continuum infimum

Coercivity and the comparison are proved on the literal
TF carrier; no minimizer, diffuse-trial hypothesis or infimum convergence is
assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace LiebThirring.TFCoulomb

private instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by norm_num [ENNReal.le_div_iff_mul_le]⟩

/-- The TF functional with the regular capped nuclear potential. -/
noncomputable def regularTFFunctional {M : ℕ} (a δ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) : ℝ :=
  a * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
    (∫ x : Position, tfCappedNuclearPotential δ z R x * ρ.val x) + tfCoulombEnergy ρ ρ

/-- Exact-mass regular TF competitor values. -/
def regularTFValues {M : ℕ} (a ν δ : ℝ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : Set ℝ :=
  {E | ∃ ρ : TFDensity, tfMass ρ = ν ∧ E = regularTFFunctional a δ z R ρ}

/-- Real exact-mass regular TF infimum, used below only after domain bounds. -/
noncomputable def regularTFInfimum {M : ℕ} (a ν δ : ℝ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ := sInf (regularTFValues a ν δ z R)

theorem regularDiscreteTFFunctional_le_regularTFFunctional {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (a : ℝ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) :
    regularDiscreteTFFunctional a δ ℓ z R ρ ≤ regularTFFunctional a δ z R ρ := by
  have hv := (box_attraction_sub_bounds hδ hℓ z R ρ).1
  have hd := tfBoxCoulombEnergy_le hℓ ρ
  unfold regularDiscreteTFFunctional regularTFFunctional
  linarith only [hv, hd]

theorem box_attraction_le {M : ℕ} {δ ℓ : ℝ} (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) :
    (∫ x : Position, boxCappedPotential δ ℓ z R x * ρ.val x) ≤
      ((∑ k : Fin M, (z k : ℝ)) / δ) * tfMass ρ := by
  rw [tfMass, ← integral_const_mul]
  apply integral_mono_ae (integrable_boxCappedPotential_mul_tfDensity hδ hℓ z R ρ)
    ((TFFunctional.integrable_tfDensity ρ).const_mul _)
  filter_upwards [TFFunctional.tfDensity_ae_nonneg ρ] with x hx
  exact mul_le_mul_of_nonneg_right (boxCappedPotential_le hδ hℓ z R x) hx

theorem regularDiscreteTFFunctional_lower {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (a : ℝ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) :
    a * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
      ((∑ k : Fin M, (z k : ℝ)) / δ) * tfMass ρ ≤
        regularDiscreteTFFunctional a δ ℓ z R ρ := by
  have hv := box_attraction_le hδ hℓ z R ρ
  have hd := tfBoxCoulombEnergy_nonneg ℓ ρ
  unfold regularDiscreteTFFunctional
  linarith only [hv, hd]

theorem regularDiscreteTFValues_bddBelow {M : ℕ} {a δ ℓ ν : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : BddBelow (regularDiscreteTFValues a ν δ ℓ z R) := by
  refine ⟨-((∑ k : Fin M, (z k : ℝ)) / δ) * ν, ?_⟩
  rintro E ⟨ρ, hm, rfl⟩
  have h := regularDiscreteTFFunctional_lower hδ hℓ a z R ρ
  rw [hm] at h
  have hk := mul_nonneg ha (TFFunctional.integral_tfDensity_rpow_five_thirds_nonneg ρ)
  linarith only [h, hk]

theorem regularTFValues_bddBelow {M : ℕ} {a δ ν : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    BddBelow (regularTFValues a ν δ z R) := by
  obtain ⟨C, hC⟩ := regularDiscreteTFValues_bddBelow (ν := ν) ha hδ zero_lt_one z R
  refine ⟨C, ?_⟩
  rintro E ⟨ρ, hm, rfl⟩
  exact (hC ⟨ρ, hm, rfl⟩).trans
    (regularDiscreteTFFunctional_le_regularTFFunctional hδ zero_lt_one a z R ρ)

theorem regularDiscreteTFValues_nonempty {M : ℕ} (a δ ℓ : ℝ) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (regularDiscreteTFValues a (ν : ℝ) δ ℓ z R).Nonempty := by
  obtain ⟨ρ, hm⟩ := TFFunctional.exists_tfDensity_mass ν
  exact ⟨_, ρ, hm, rfl⟩

/-- The uniform L^(5/3) bound follows from the actual regular functional. -/
theorem norm_le_of_regularDiscreteTFFunctional_le {M : ℕ} {a δ ℓ ν E : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hm : tfMass ρ = ν)
    (hE : regularDiscreteTFFunctional a δ ℓ z R ρ ≤ E) :
    (eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume).toReal ≤
      (max 0 ((E + ((∑ k : Fin M, (z k : ℝ)) / δ) * ν) / a)) ^ ((3 : ℝ) / 5) := by
  have hlower := regularDiscreteTFFunctional_lower hδ hℓ a z R ρ
  rw [hm, TFFunctional.integral_tfDensity_rpow_eq_norm] at hlower
  have hk : ‖ρ.val‖ ^ ((5 : ℝ) / 3) ≤
      (E + ((∑ k : Fin M, (z k : ℝ)) / δ) * ν) / a := by
    apply (le_div_iff₀ ha).mpr
    linarith only [hlower, hE]
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg ρ.val) _) (hk.trans (le_max_right 0 _))
    (by norm_num : (0 : ℝ) ≤ 3 / 5)
  rw [← Real.rpow_mul (norm_nonneg ρ.val)] at hr
  norm_num only [show (5 / 3 : ℝ) * (3 / 5) = 1 by norm_num, Real.rpow_one] at hr
  simpa only [Lp.norm_def] using hr

/-- Uniform eventual lower comparison of the two exact-mass infima. -/
theorem regularTFInfimum_le_discrete_add {M : ℕ} {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ ℓ : ℝ, 0 < ℓ → ℓ < η →
      regularTFInfimum a (ν : ℝ) δ z R - ε ≤ regularDiscreteTFInfimum a (ν : ℝ) δ ℓ z R := by
  let e := regularTFInfimum a (ν : ℝ) δ z R
  let B₀ := (max 0 ((e + 1 + ((∑ k : Fin M, (z k : ℝ)) / δ) * ν) / a)) ^ ((3 : ℝ) / 5)
  have hB : 0 ≤ B₀ := Real.rpow_nonneg (le_max_left _ _) _
  obtain ⟨ηD, hηD, hD⟩ := tfBoxCoulombEnergy_uniform ν.property hB (ε / 2) (half_pos hε)
  let L := Real.sqrt 3 * (∑ k : Fin M, (z k : ℝ)) / δ ^ 2 * (ν : ℝ)
  have hL : 0 ≤ L := by positivity
  let ηV := (ε / 2) / (L + 1)
  have hηV : 0 < ηV := div_pos (half_pos hε) (by linarith only [hL])
  refine ⟨min ηD ηV, lt_min hηD hηV, fun ℓ hℓ hη => ?_⟩
  apply le_csInf (regularDiscreteTFValues_nonempty a δ ℓ ν z R)
  rintro E ⟨ρ, hm, rfl⟩
  by_cases hE : regularDiscreteTFFunctional a δ ℓ z R ρ ≤ e + 1
  · have hn := norm_le_of_regularDiscreteTFFunctional_le ha hδ hℓ z R ρ hm hE
    obtain ⟨_, hderr⟩ := hD ℓ hℓ (lt_of_lt_of_le hη (min_le_left _ _)) ρ hm.le hn
    have hv := (box_attraction_sub_bounds hδ hℓ z R ρ).2
    rw [hm] at hv
    have hvsmall : L * ℓ < ε / 2 := by
      have h := (lt_div_iff₀ (by linarith only [hL] : 0 < L + 1)).mp
        (lt_of_lt_of_le hη (min_le_right _ _))
      have hl : L * ℓ ≤ ℓ * (L + 1) := by nlinarith only [hℓ.le]
      exact hl.trans_lt h
    have hveq : (Real.sqrt 3 * (∑ k : Fin M, (z k : ℝ)) * ℓ / δ ^ 2) * ν = L * ℓ := by
      dsimp only [L]
      ring
    rw [hveq] at hv
    have he : e ≤ regularTFFunctional a δ z R ρ :=
      csInf_le (regularTFValues_bddBelow ha.le hδ z R) ⟨ρ, hm, rfl⟩
    unfold regularTFFunctional at he
    unfold regularDiscreteTFFunctional at hE ⊢
    linarith only [he, hv, hvsmall, hderr]
  · have he := lt_of_not_ge hE
    change e - ε ≤ _
    linarith only [he, hε]

theorem regularTFValues_nonempty {M : ℕ} (a δ : ℝ) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (regularTFValues a (ν : ℝ) δ z R).Nonempty := by
  obtain ⟨ρ, hm⟩ := TFFunctional.exists_tfDensity_mass ν
  exact ⟨_, ρ, hm, rfl⟩

end LiebThirring.TFCoulomb

end
