/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.KineticPairBound
public import LiebThirring.TFMinimizer.SlackVariation

/-! # A slack TF minimizer cannot be positively charged

An elementary variational alternative to Lieb–Simon (1977) II.18's
spherical Jensen argument. A proportional-thickness annulus gives a Coulomb
first variation of order `L²`, while Holder bounds its kinetic variation by
`L^(9/5)`. Taking `L=T^5` reduces the strict growth comparison to integer powers.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

/-- The actual annulus competitor inequality under a slack mass cap. -/
theorem annulus_firstVariation_inequality {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ < (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R)
    (L : ℝ) (hL : 0 < L) (hR : ∀ k, ‖R k‖ ≤ L)
    (hcharge : tfMass ρ ≤ totalNuclearCharge z) :
    (totalNuclearCharge z - tfMass ρ) *
      (tfMass (tfAnnulusDensity L) / (2 * L)) ≤
        (5 / 3 : ℝ) * a.val *
          (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((2 : ℝ) / 5) *
          (tfMass (tfAnnulusDensity L)) ^ ((3 : ℝ) / 5) := by
  let σ := tfAnnulusDensity L
  let c : ℝ := (coulombPotential (tfDensityMeasure σ) 0).toReal
  have hA : (∫ x : Position, tfNuclearPotential z R x * σ.val x) = totalNuclearCharge z * c := by
    rw [integral_tfNuclearPotential_mul_eq_sum_potential]
    dsimp only [σ]
    simp_rw [potential_tfAnnulusDensity_cavity L (R _) (hR _)]
    exact (Finset.sum_mul ..).symm
  have hD : 2 * tfCoulombEnergy ρ σ ≤ tfMass ρ * c := by
    rw [tfCoulombEnergy_symm, ← integral_potential_pair]
    have hp : ∀ x : Position, (coulombPotential (tfDensityMeasure σ) x).toReal ≤ c := by
      intro x
      exact ENNReal.toReal_mono (coulombPotential_tfDensityMeasure_lt_top σ 0).ne
        (potential_tfAnnulusDensity_le_center L x)
    have hle : ∀ᵐ x ∂(volume : Measure Position),
        (coulombPotential (tfDensityMeasure σ) x).toReal * ρ.val x ≤ c * ρ.val x := by
      filter_upwards [tfDensity_ae_nonneg ρ] with x hx
      exact mul_le_mul_of_nonneg_right (hp x) hx
    have h := integral_mono_ae (integrable_potential_pair σ ρ)
      ((integrable_tfDensity ρ).const_mul c) hle
    rw [integral_const_mul] at h
    simpa only [tfMass, mul_comm] using h
  have hK := integral_kinetic_pair_le ρ σ
  rw [integral_kinetic_tfAnnulusDensity L] at hK
  have hI := integral_tfFirstVariation_pair_nonneg_of_mass_lt a ν z R ρ hmass hmin σ
  rw [integral_tfFirstVariation_pair] at hI
  have hcoef : 0 ≤ (5 / 3 : ℝ) * a.val := mul_nonneg (by norm_num) a.property.le
  have hupper := mul_le_mul_of_nonneg_left hK hcoef
  have hc := mass_div_le_potential_tfAnnulusDensity_center L hL
  have hlower := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hcharge)
  change _ ≤ _ at hlower
  rw [hA] at hI
  nlinarith only [hlower, hI, hD, hupper]

/-- Under a slack cap, the actual relaxed minimizer has at least the nuclear charge. -/
theorem totalNuclearCharge_le_tfMass_of_mass_lt {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) (hmass : tfMass ρ < (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    totalNuclearCharge z ≤ tfMass ρ := by
  by_contra hn
  have hcharge : tfMass ρ < totalNuclearCharge z := lt_of_not_ge hn
  let δ : ℝ := totalNuclearCharge z - tfMass ρ
  let b : ℝ := 7 * ballVolumeConstant
  let C : ℝ := (5 / 3 : ℝ) * a.val *
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((2 : ℝ) / 5)
  let D : ℝ := δ * b / 2
  have hδ : 0 < δ := sub_pos.mpr hcharge
  have hb : 0 < b := mul_pos (by norm_num) ballVolumeConstant_pos
  have hD : 0 < D := div_pos (mul_pos hδ hb) (by norm_num)
  obtain ⟨T, hT⟩ := exists_gt (max (max (1 : ℝ) (∑ k : Fin M, ‖R k‖))
    (C * b ^ ((3 : ℝ) / 5) / D))
  have hT1 : 1 < T := lt_of_le_of_lt
    ((le_max_left 1 (∑ k : Fin M, ‖R k‖)).trans (le_max_left _ _)) hT
  have hTpos : 0 < T := zero_lt_one.trans hT1
  have hTS : (∑ k : Fin M, ‖R k‖) < T := lt_of_le_of_lt
    ((le_max_right 1 (∑ k : Fin M, ‖R k‖)).trans (le_max_left _ _)) hT
  have hTC : C * b ^ ((3 : ℝ) / 5) / D < T := lt_of_le_of_lt (le_max_right _ _) hT
  have hpow : T ≤ T ^ 5 := le_self_pow₀ hT1.le (by norm_num)
  have hR : ∀ k, ‖R k‖ ≤ T ^ 5 := by
    intro k
    exact (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => norm_nonneg (R i))
      (Finset.mem_univ k)).trans (hTS.le.trans hpow)
  have hi := annulus_firstVariation_inequality a ν z R ρ hmass hmin
    (T ^ 5) (pow_pos hTpos 5) hR hcharge.le
  rw [tfMass_tfAnnulusDensity _ (pow_pos hTpos 5)] at hi
  have hleft : (totalNuclearCharge z - tfMass ρ) *
      (7 * ballVolumeConstant * (T ^ 5) ^ 3 / (2 * T ^ 5)) = (D * T) * T ^ 9 := by
    dsimp [D, δ, b]
    field_simp
  have hright : (7 * ballVolumeConstant * (T ^ 5) ^ 3) ^ ((3 : ℝ) / 5) =
      b ^ ((3 : ℝ) / 5) * T ^ 9 := by
    change (b * (T ^ 5) ^ 3) ^ ((3 : ℝ) / 5) = _
    rw [Real.mul_rpow hb.le (by positivity), ← pow_mul,
      ← Real.rpow_natCast_mul hTpos.le]
    norm_num
  rw [hleft, hright] at hi
  have he : (5 / 3 : ℝ) * a.val *
      (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((2 : ℝ) / 5) *
        (b ^ ((3 : ℝ) / 5) * T ^ 9) = (C * b ^ ((3 : ℝ) / 5)) * T ^ 9 := by
    dsimp [C]
    ring
  rw [he] at hi
  have hlo := (mul_le_mul_iff_of_pos_right (pow_pos hTpos 9)).mp hi
  have hstrict : C * b ^ ((3 : ℝ) / 5) < D * T := by
    simpa only [mul_comm] using (div_lt_iff₀ hD).mp hTC
  exact (not_lt_of_ge hlo) hstrict

end LiebThirring.TFMinimizer

end
