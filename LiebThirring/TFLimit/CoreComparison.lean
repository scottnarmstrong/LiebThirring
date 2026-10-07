/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCore.CutoffComparison
public import LiebThirring.TFQuantum.DilationLargeCharge
public import LiebThirring.TFQuantum.SlaterCoulomb
public import LiebThirring.TFCoulomb.RegularDiscrete

/-! # Paying for cutoff loss in the normalized Hamiltonian

The actual quantum density-testing identities turn the
proved core estimate into comparison with the regular scaled form. No
state/sector-dependent parameter is chosen.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFLimit

theorem integrable_nuclearPotential_density {N q M : ℕ}
    (ψ : FormDomain N q) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Integrable (fun x : Position => tfNuclearPotential z R x * (density ψ.val x).toReal) := by
  let w : Position → ℝ≥0∞ := fun x => ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel x (R k)
  have hw : Measurable w := Finset.measurable_sum _ (fun _ _ =>
    measurable_const.mul measurable_coulombKernel.of_uncurry_right)
  have hf : (∫⁻ x : Position, w x * density ψ.val x) < ⊤ := by
    rw [← attraction_expectation_eq_density ψ.val z R]
    exact lintegral_attraction_lt_top z R ψ.val ψ.property.2
  apply (integrable_toReal_of_lintegral_ne_top
    (hw.mul (measurable_density ψ.val)).aemeasurable hf.ne).congr
  filter_upwards [nuclearPotential_ennreal_toReal z R] with x hx
  change (w x * density ψ.val x).toReal = _
  rw [ENNReal.toReal_mul, hx]

/-- The bounded cap has a finite density test, including the vacuum. -/
theorem lintegral_capped_density_lt_top {N q M : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (ψ : FormDomain N q) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (∫⁻ x : Position, ENNReal.ofReal (tfCappedNuclearPotential δ z R x) *
      density ψ.val x) < ⊤ := by
  apply lt_of_le_of_lt (lintegral_mono (fun x =>
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (tfCappedNuclearPotential_le hδ z R x)) _))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, density_mass]
  finiteness

/-- Exact density testing for the canonical capped attraction expectation. -/
theorem cappedAttractionExpectation_eq_density {N q M : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (ψ : FormDomain N q) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    TFCoulomb.cappedAttractionExpectation δ z R ψ =
      ∫ x : Position, tfCappedNuclearPotential δ z R x * (density ψ.val x).toReal := by
  have hv := (continuous_tfCappedNuclearPotential hδ z R).measurable
  have he : (∫⁻ X : Configuration N, ENNReal.ofReal
      (∑ i : Fin N, tfCappedNuclearPotential δ z R (particlePosition X i)) *
        (‖ψ.val X‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Position, ENNReal.ofReal (tfCappedNuclearPotential δ z R x) * density ψ.val x := by
    rw [density_testing N q ψ.val _ hv.ennreal_ofReal]
    have hs (X : Configuration N) : ENNReal.ofReal
        (∑ i : Fin N, tfCappedNuclearPotential δ z R (particlePosition X i)) =
        ∑ i : Fin N, ENNReal.ofReal (tfCappedNuclearPotential δ z R (particlePosition X i)) :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => tfCappedNuclearPotential_nonneg hδ z R _)
    simp_rw [hs, Finset.sum_mul]
    exact lintegral_finsetSum _ (fun i _ =>
      ((hv.comp (measurable_particlePosition i)).ennreal_ofReal.mul (measurable_state_norm_sq ψ.val)))
  have hm := hv.ennreal_ofReal.mul (measurable_density ψ.val)
  have hf := lintegral_capped_density_lt_top δ hδ ψ z R
  unfold TFCoulomb.cappedAttractionExpectation
  rw [he]
  refine (integral_toReal hm.aemeasurable (ae_lt_top hm hf.ne)).symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp only [Pi.mul_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (tfCappedNuclearPotential_nonneg hδ z R x)]

theorem integrable_cappedPotential_density {N q M : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (ψ : FormDomain N q) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Integrable (fun x : Position => tfCappedNuclearPotential δ z R x * (density ψ.val x).toReal) := by
  have hv := (continuous_tfCappedNuclearPotential hδ z R).measurable
  have hf := lintegral_capped_density_lt_top δ hδ ψ z R
  apply (integrable_toReal_of_lintegral_ne_top
    (hv.ennreal_ofReal.mul (measurable_density ψ.val)).aemeasurable hf.ne).congr
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only [Pi.mul_apply]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (tfCappedNuclearPotential_nonneg hδ z R x)])

private theorem scaled_core_coefficients (α η : ℝ) (hα : 0 < α) (hη : 0 < η) :
    α⁻¹ * (η * α ^ (-(2 : ℝ) / 3)) = α ^ (-(5 : ℝ) / 3) * η ∧
    α⁻¹ * (η * α ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 2) = η ^ (-(3 : ℝ) / 2) := by
  constructor
  · rw [← Real.rpow_neg_one, ← mul_assoc, mul_comm (α ^ (-1 : ℝ)) η,
      mul_assoc, ← Real.rpow_add hα]
    norm_num
    ring
  · rw [Real.mul_rpow hη.le (Real.rpow_nonneg hα.le _), ← Real.rpow_mul hα.le]
    norm_num
    rw [← mul_assoc, mul_comm α⁻¹, mul_assoc, inv_mul_cancel₀ hα.ne', mul_one]

private theorem kinetic_fraction_compare (T B A V c s η : ℝ)
    (h : -c ≤ s * η * T - (A - V)) :
    s * (1 - η) * T + B - V - c ≤ s * T + B - A := by
  nlinarith only [h]

/-- The normalized uncut form exceeds the regular form minus the uniform core error. -/
theorem regularScaledQuantumEnergy_sub_core_le {N q M : ℕ}
    (hq : 1 ≤ q) (α : ℝ≥0) (hα : 0 < α) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ψ : FormDomain N q) (hnorm : ‖ψ.val‖ = 1) :
    TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ -
        TFCore.coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ ≤
      dilatedElectronicEnergy α z R ψ := by
  have hαr : 0 < (α : ℝ) := hα
  have hη' : 0 < η * (α : ℝ) ^ (-(2 : ℝ) / 3) :=
    mul_pos hη (Real.rpow_pos_of_pos hαr _)
  have hcore := (TFCore.cutoff_loss_bound q hq N M ψ.val ψ.property.1 hnorm
    ψ.property.2 _ δ hη' hδ z R).2
  simp_rw [sub_mul] at hcore
  rw [integral_sub (integrable_nuclearPotential_density ψ z R)
    (integrable_cappedPotential_density δ hδ ψ z R),
    ← attraction_expectation_toReal_eq_density ψ.val z R ψ.property.2,
    ← cappedAttractionExpectation_eq_density δ hδ ψ z R] at hcore
  have hscaled := mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr hαr.le)
  rw [mul_neg, mul_sub] at hscaled
  have hc := scaled_core_coefficients (α : ℝ) η hαr hη
  have he : (α : ℝ)⁻¹ * (TFCore.coreErrorConstant q z *
      (η * (α : ℝ) ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 2) * Real.sqrt δ) =
      TFCore.coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ := by
    calc
      _ = TFCore.coreErrorConstant q z * Real.sqrt δ *
        ((α : ℝ)⁻¹ * (η * (α : ℝ) ^ (-(2 : ℝ) / 3)) ^ (-(3 : ℝ) / 2)) := by ring
      _ = _ := by rw [hc.2]; ring
  rw [he, ← mul_assoc, hc.1] at hscaled
  have hp : (α : ℝ) ^ (-(2 : ℝ)) = (α : ℝ)⁻¹ ^ 2 := by
    rw [Real.rpow_neg hαr.le, Real.rpow_two, inv_pow]
  unfold TFCoulomb.regularScaledQuantumEnergy dilatedElectronicEnergy
  rw [hp, Real.rpow_neg_one]
  unfold TFCoulomb.repulsionExpectation
  rw [mul_sub] at hscaled
  exact kinetic_fraction_compare _ _ _ _ _ _ _ hscaled

end LiebThirring.TFLimit
end
