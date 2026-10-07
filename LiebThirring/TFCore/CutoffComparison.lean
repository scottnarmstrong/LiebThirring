/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCore.NuclearCores
public import LiebThirring.TFCoulomb.RegularPotential

/-! # Comparing the capped and singular nuclear potentials

Capping decreases the potential off the nuclei and hence
almost everywhere. This qualification is necessary for the real
potential, since real division assigns zero to a Coulomb pole. The loss is
bounded by the core sum with exactly the radius used in nuclear-core estimate.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFCore

/-- The elementary comparison away from the finitely many poles. -/
theorem capped_nuclearPotential_le_of_ne {M : ℕ} (δ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position)
    (hx : ∀ k, x ≠ R k) :
    tfCappedNuclearPotential δ z R x ≤ tfNuclearPotential z R x := by
  unfold tfCappedNuclearPotential tfNuclearPotential
  apply Finset.sum_le_sum
  intro k _
  exact div_le_div_of_nonneg_left (z k).property
    (norm_pos_iff.mpr (sub_ne_zero.mpr (hx k))) (le_max_right _ _)

/-- The pole convention disappears under Lebesgue integration. -/
theorem capped_nuclearPotential_le_ae {M : ℕ} (δ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∀ᵐ x : Position, tfCappedNuclearPotential δ z R x ≤ tfNuclearPotential z R x := by
  have hn : ∀ᵐ x : Position, ∀ k : Fin M, x ≠ R k :=
    ae_all_iff.mpr (fun k => volume.ae_ne (R k))
  filter_upwards [hn] with x hx
  exact capped_nuclearPotential_le_of_ne δ z R x hx

/-- Each real one-core value agrees with the extended cutoff's real part. -/
theorem nucleusCutoff_toReal (a r : ℝ) (ha : 0 ≤ a) (R x : Position) :
    (Assembly.nucleusCutoff a r R x).toReal =
      if ‖x - R‖ < r then a / ‖x - R‖ else 0 := by
  unfold Assembly.nucleusCutoff
  split_ifs <;> simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (norm_nonneg _),
    div_eq_mul_inv, ENNReal.toReal_zero]

/-- The capped-potential loss is bounded by the real core sum off the poles. -/
theorem nuclearPotential_sub_capped_le_of_ne {M : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Position) (hx : ∀ k, x ≠ R k) :
    tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x ≤
      (nuclearCores z R δ x).toReal := by
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin M)),
      Assembly.nucleusCutoff (z k : ℝ) δ (R k) x ≠ ⊤ := by
    intro k _
    unfold Assembly.nucleusCutoff
    split_ifs
    · exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.inv_lt_top.mpr
          (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr (hx k)))))).ne
    · exact ENNReal.zero_ne_top
  unfold tfNuclearPotential tfCappedNuclearPotential nuclearCores
  rw [← Finset.sum_sub_distrib, ENNReal.toReal_sum hf]
  apply Finset.sum_le_sum
  intro k _
  rw [nucleusCutoff_toReal (z k : ℝ) δ (z k).property (R k) x]
  by_cases hk : ‖x - R k‖ < δ
  · rw [ite_eq_left hk, max_eq_left hk.le]
    exact sub_le_self _ (div_nonneg (z k).property hδ.le)
  · rw [ite_eq_right hk, max_eq_right (le_of_not_gt hk), sub_self]

theorem nuclearPotential_sub_capped_le_ae {M : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∀ᵐ x : Position, tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x ≤
      (nuclearCores z R δ x).toReal := by
  have hn : ∀ᵐ x : Position, ∀ k : Fin M, x ≠ R k :=
    ae_all_iff.mpr (fun k => volume.ae_ne (R k))
  filter_upwards [hn] with x hx
  exact nuclearPotential_sub_capped_le_of_ne δ hδ z R x hx

/-- The extended density testing form of the cutoff loss is controlled by nuclear-core estimate. -/
theorem lintegral_cutoff_loss_density_le (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (ψ : State N q) (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (∫⁻ x : Position, ENNReal.ofReal
      (tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x) * density ψ x) ≤
      ENNReal.ofReal η * kineticEnergy ψ +
        ENNReal.ofReal (coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ) := by
  apply le_trans _ (lintegral_nuclearCores_density_le q hq N M ψ hanti hnorm
    η δ hη hδ z R)
  apply lintegral_mono_ae
  filter_upwards [nuclearPotential_sub_capped_le_ae δ hδ z R] with x hx
  exact mul_le_mul_left ((ENNReal.ofReal_le_ofReal hx).trans ENNReal.ofReal_toReal_le) _

/-- The cutoff loss is integrable and paid for by ηT in the real quadratic form. -/
theorem cutoff_loss_bound (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (ψ : State N q) (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (hT : kineticEnergy ψ < ⊤) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Integrable (fun x : Position =>
      (tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x) * (density ψ x).toReal) ∧
      -(coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ) ≤
        η * (kineticEnergy ψ).toReal - ∫ x : Position,
          (tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x) *
            (density ψ x).toReal := by
  have hv : Measurable (fun x : Position =>
      tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x) := by
    apply Measurable.sub _ (continuous_tfCappedNuclearPotential hδ z R).measurable
    exact Finset.measurable_sum _ (fun _ _ =>
      measurable_const.div ((measurable_id.sub measurable_const).norm))
  have hn : ∀ᵐ x : Position,
      0 ≤ tfNuclearPotential z R x - tfCappedNuclearPotential δ z R x :=
    (capped_nuclearPotential_le_ae δ z R).mono (fun _ hx => sub_nonneg.mpr hx)
  have hext := lintegral_cutoff_loss_density_le q hq N M ψ hanti hnorm η δ hη hδ z R
  have hfin : ENNReal.ofReal η * kineticEnergy ψ +
      ENNReal.ofReal (coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ) < ⊤ := by
    finiteness
  obtain ⟨hi, hreal⟩ := real_density_testing_of_lintegral_le ψ _ hv hn _ hfin hext
  refine ⟨hi, ?_⟩
  have hc : 0 ≤ coreErrorConstant q z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ :=
    mul_nonneg (mul_nonneg (coreErrorConstant_nonneg q z) (Real.rpow_nonneg hη.le _))
      (Real.sqrt_nonneg _)
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le, ENNReal.toReal_ofReal hc] at hreal
  linarith only [hreal]

end LiebThirring.TFCore
end
