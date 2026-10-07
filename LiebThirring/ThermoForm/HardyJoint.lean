/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.HardyNuclear
public import LiebThirring.ThermoStability.FibreMeasurability
public import LiebThirring.Thermodynamic.QuantumFormDomain

/-! # Quantitative Coulomb bounds for joint quantum states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring

open ThermoStability

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The nuclear-repulsion part of the joint expectation, in nuclear fibres. -/
theorem joint_nuclearRepulsion_eq_fibre_lintegral {N M q : ℕ} (z : ℕ)
    (ψ : QuantumState N M q) :
    (∫⁻ X : QuantumConfiguration N M,
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration N, ∫⁻ R : Configuration M,
        nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition R k) * ‖nuclearFibreField ψ x R‖ₑ ^ 2 := by
  let w : Configuration M → ℝ≥0∞ := fun R =>
    nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k)
  have hw : Measurable w := by
    unfold w nuclearRepulsion
    refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    exact measurable_const.mul ((measurable_particlePosition k).sub
      (measurable_particlePosition l)).norm.ennreal_ofReal.inv
  have hfull := lintegral_weight_electronFibreField ψ
    (fun X : QuantumConfiguration N M => w X.snd)
    (hw.comp (continuous_snd.comp (WithLp.prod_continuous_ofLp ..)).measurable)
  have hswap := blockSwapCurrying_weighted_norm_sq (electronFibreField ψ) w hw
  rw [blockSwap_electronFibreField] at hswap
  have hcollapse : (∫⁻ R : Configuration M, ∫⁻ x : Configuration N,
      w R * ‖electronFibreField ψ R x‖ₑ ^ 2) =
      ∫⁻ R : Configuration M, w R * ‖electronFibreField ψ R‖ₑ ^ 2 := by
    apply lintegral_congr
    intro R
    rw [lintegral_const_mul (w R)
      ((Lp.stronglyMeasurable (electronFibreField ψ R)).enorm.pow_const 2),
      lintegral_l2_enorm_sq]
  exact hfull.trans (hcollapse.trans hswap.symm)

/-- Joint attraction is controlled by electronic mass and kinetic energy. -/
theorem quantumAttractionEnergy_le_formBound {N M q : ℕ} (z : ℕ)
    (ψ : QuantumState N M q) :
    quantumAttractionEnergy z ψ ≤
      (∑ _i : Fin N, ∑ _k : Fin M, (z : ℝ≥0∞)) *
        (‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ) := by
  let C : ℝ≥0∞ := ∑ _i : Fin N, ∑ _k : Fin M, (z : ℝ≥0∞)
  rw [quantumAttractionEnergy_eq_fibre_lintegral]
  calc
    _ ≤ ∫⁻ R : Configuration M, C *
        (‖electronFibreField ψ R‖ₑ ^ 2 + 4 * kineticEnergy (electronFibreField ψ R)) := by
      apply lintegral_mono
      intro R
      apply (lintegral_attraction_le_mass_add_totalKinetic
        (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k)
        (electronFibreField ψ R)).trans_eq
      simp only [C, enorm_eq_nnnorm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      apply Finset.sum_congr rfl
      intro _ _
      norm_cast
    _ = C * (∫⁻ R : Configuration M,
        ‖electronFibreField ψ R‖ₑ ^ 2 + 4 * kineticEnergy (electronFibreField ψ R)) := by
      rw [lintegral_const_mul' C _ (by
        apply ENNReal.sum_ne_top.mpr
        intro _ _
        exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.coe_ne_top)]
    _ = C * ((∫⁻ R : Configuration M, ‖electronFibreField ψ R‖ₑ ^ 2) +
        4 * ∫⁻ R : Configuration M, kineticEnergy (electronFibreField ψ R)) := by
      rw [lintegral_add_left' ((Lp.stronglyMeasurable
        (electronFibreField ψ)).enorm.pow_const 2).aemeasurable,
        lintegral_const_mul' 4 _ (by norm_num)]
    _ = _ := by
      rw [lintegral_l2_enorm_sq, ← quantumElectronKineticEnergy_eq_fibre_lintegral]
      have hn := electronFibreField_norm ψ
      have he : ‖electronFibreField ψ‖ₑ = ‖ψ‖ₑ := by
        simpa only [← ofReal_norm] using congrArg ENNReal.ofReal hn
      rw [he]

/-- Constant nuclear charges factor out of the pair repulsion. -/
theorem nuclearRepulsion_const_eq (M z : ℕ) (R : Configuration M) :
    nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) =
      (z : ℝ≥0∞) ^ 2 * electronRepulsion R := by
  unfold nuclearRepulsion electronRepulsion
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((z : ℝ≥0∞) * (z : ℝ≥0∞)) * _ = (z : ℝ≥0∞) ^ 2 * _
  rw [pow_two]

/-- Joint nuclear repulsion is controlled by nuclear mass and kinetic energy. -/
theorem quantumNuclearRepulsionEnergy_le_formBound {N M q : ℕ} (z : ℕ)
    (ψ : QuantumState N M q) :
    (∫⁻ X : QuantumConfiguration N M,
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      ((z : ℝ≥0∞) ^ 2 *
        (∑ _σ : SpinLabels N q, ∑ _i : Fin M,
          ∑ _j ∈ Finset.univ.filter (fun j => _i < j), 1)) *
        (‖ψ‖ₑ ^ 2 + 4 * quantumNuclearKineticEnergy ψ) := by
  let C : ℝ≥0∞ := (z : ℝ≥0∞) ^ 2 *
    (∑ _σ : SpinLabels N q, ∑ i : Fin M,
      ∑ _j ∈ Finset.univ.filter (fun j => i < j), 1)
  rw [joint_nuclearRepulsion_eq_fibre_lintegral]
  calc
    _ = ∫⁻ x : Configuration N, (z : ℝ≥0∞) ^ 2 *
        (∫⁻ R : Configuration M, electronRepulsion R *
          ‖nuclearFibreField ψ x R‖ₑ ^ 2) := by
      apply lintegral_congr
      intro x
      rw [← lintegral_const_mul' ((z : ℝ≥0∞) ^ 2) _ (by finiteness)]
      apply lintegral_congr
      intro R
      rw [nuclearRepulsion_const_eq]
      ac_rfl
    _ ≤ ∫⁻ x : Configuration N, C *
        (‖nuclearFibreField ψ x‖ₑ ^ 2 +
          4 * finiteTargetKineticEnergy (nuclearFibreField ψ x)) := by
      apply lintegral_mono
      intro x
      apply (mul_le_mul_of_nonneg_left
        (lintegral_electronRepulsion_finiteTarget_le_common (nuclearFibreField ψ x))
        zero_le).trans_eq
      simp only [C, enorm_eq_nnnorm]
      rw [mul_assoc]
      congr 1
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_mul]
      simp only [one_mul]
    _ = C * (∫⁻ x : Configuration N,
        ‖nuclearFibreField ψ x‖ₑ ^ 2 +
          4 * finiteTargetKineticEnergy (nuclearFibreField ψ x)) := by
      rw [lintegral_const_mul' C _ (by
        apply ENNReal.mul_ne_top (by finiteness)
        apply ENNReal.sum_ne_top.mpr
        intro _ _
        exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.sum_ne_top.mpr fun _ _ => by norm_num)]
    _ = C * ((∫⁻ x : Configuration N, ‖nuclearFibreField ψ x‖ₑ ^ 2) +
        4 * ∫⁻ x : Configuration N,
          finiteTargetKineticEnergy (nuclearFibreField ψ x)) := by
      rw [lintegral_add_left' ((Lp.stronglyMeasurable
        (nuclearFibreField ψ)).enorm.pow_const 2).aemeasurable,
        lintegral_const_mul' 4 _ (by norm_num)]
    _ = _ := by
      rw [lintegral_l2_enorm_sq]
      change C * (‖nuclearFibreField ψ‖ₑ ^ 2 + 4 *
        (∫⁻ x : Configuration N, finiteTargetKineticEnergy (nuclearFibreField ψ x))) =
        C * (‖ψ‖ₑ ^ 2 + 4 * quantumNuclearKineticEnergy ψ)
      have hk : (∫⁻ x : Configuration N,
          finiteTargetKineticEnergy (nuclearFibreField ψ x)) =
          quantumNuclearKineticEnergy ψ := by
        exact (quantumNuclearKineticEnergy_eq_fibre_lintegral ψ).symm
      have hn : ‖nuclearFibreField ψ‖ = ‖ψ‖ := by
        rw [← (blockSwapCurrying (E := SpinAmplitudes N q)).norm_map
          (nuclearFibreField ψ), blockSwap_nuclearFibreField, electronFibreField_norm]
      have he : ‖nuclearFibreField ψ‖ₑ = ‖ψ‖ₑ := by
        simpa only [← ofReal_norm] using congrArg ENNReal.ofReal hn
      exact congrArg (fun t : ℝ≥0∞ => C * t)
        (congrArg₂ (fun a b : ℝ≥0∞ => a ^ 2 + 4 * b) he hk)

/-- The electron-electron part of the joint repulsion has the electronic form bound. -/
theorem quantumElectronRepulsionEnergy_le_formBound {N M q : ℕ}
    (ψ : QuantumState N M q) :
    (∫⁻ X : QuantumConfiguration N M,
      electronRepulsion X.fst * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      (∑ _i : Fin N, ∑ _j ∈ Finset.univ.filter (fun j => _i < j), 1) *
        (‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ) := by
  let C : ℝ≥0∞ :=
    ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (fun j => i < j), 1
  have hw : Measurable (fun X : QuantumConfiguration N M => electronRepulsion X.fst) :=
    Assembly.measurable_electronRepulsion.comp
      (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable
  rw [lintegral_weight_electronFibreField ψ _ hw]
  calc
    _ ≤ ∫⁻ R : Configuration M, C *
        (‖electronFibreField ψ R‖ₑ ^ 2 + 4 * kineticEnergy (electronFibreField ψ R)) := by
      apply lintegral_mono
      intro R
      apply (lintegral_electronRepulsion_le_mass_add_totalKinetic
        (electronFibreField ψ R)).trans_eq
      simp only [C, enorm_eq_nnnorm]
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_mul]
      simp only [one_mul]
    _ = C * (∫⁻ R : Configuration M,
        ‖electronFibreField ψ R‖ₑ ^ 2 + 4 * kineticEnergy (electronFibreField ψ R)) := by
      rw [lintegral_const_mul' C _ (by
        apply ENNReal.sum_ne_top.mpr
        intro _ _
        exact ENNReal.sum_ne_top.mpr fun _ _ => by norm_num)]
    _ = C * ((∫⁻ R : Configuration M, ‖electronFibreField ψ R‖ₑ ^ 2) +
        4 * ∫⁻ R : Configuration M, kineticEnergy (electronFibreField ψ R)) := by
      rw [lintegral_add_left' ((Lp.stronglyMeasurable
        (electronFibreField ψ)).enorm.pow_const 2).aemeasurable,
        lintegral_const_mul' 4 _ (by norm_num)]
    _ = _ := by
      rw [lintegral_l2_enorm_sq]
      change C * (‖electronFibreField ψ‖ₑ ^ 2 + 4 *
        (∫⁻ R : Configuration M, kineticEnergy (electronFibreField ψ R))) =
        C * (‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ)
      have hk := (quantumElectronKineticEnergy_eq_fibre_lintegral ψ).symm
      have hn := electronFibreField_norm ψ
      have he : ‖electronFibreField ψ‖ₑ = ‖ψ‖ₑ := by
        simpa only [← ofReal_norm] using congrArg ENNReal.ofReal hn
      exact congrArg (fun t : ℝ≥0∞ => C * t)
        (congrArg₂ (fun a b : ℝ≥0∞ => a ^ 2 + 4 * b) he hk)

/-- Both Coulomb expectations are finite on the joint form domain. -/
theorem quantum_coulombEnergy_lt_top {N M q : ℕ} (z : ℕ)
    (ψ : QuantumFormDomain N M q) :
    quantumRepulsionEnergy z ψ.val < ⊤ ∧ quantumAttractionEnergy z ψ.val < ⊤ := by
  let u : QuantumState N M q := ψ.val
  have he : quantumElectronKineticEnergy u < ⊤ := ψ.property.2.2.1
  have hn : quantumNuclearKineticEnergy u < ⊤ := ψ.property.2.2.2
  have hm : ‖u‖ₑ ^ 2 < ⊤ := ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hEe : (∫⁻ X : QuantumConfiguration N M,
      electronRepulsion X.fst * (‖u X‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    apply (quantumElectronRepulsionEnergy_le_formBound u).trans_lt
    apply ENNReal.mul_lt_top
    · apply ENNReal.sum_lt_top.mpr
      intro _ _
      exact ENNReal.sum_lt_top.mpr fun _ _ => by norm_num
    · exact ENNReal.add_lt_top.mpr ⟨hm, ENNReal.mul_lt_top (by norm_num) he⟩
  have hNn : (∫⁻ X : QuantumConfiguration N M,
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k) * (‖u X‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    apply (quantumNuclearRepulsionEnergy_le_formBound z u).trans_lt
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top (by finiteness)
      apply ENNReal.sum_lt_top.mpr
      intro _ _
      exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.sum_lt_top.mpr fun _ _ => by norm_num
    · exact ENNReal.add_lt_top.mpr ⟨hm, ENNReal.mul_lt_top (by norm_num) hn⟩
  constructor
  · unfold quantumRepulsionEnergy
    simp_rw [add_mul]
    rw [lintegral_add_left]
    · exact ENNReal.add_lt_top.mpr ⟨hEe, hNn⟩
    · exact (Assembly.measurable_electronRepulsion.comp
        (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable).mul
          ((Lp.stronglyMeasurable u).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  · apply (quantumAttractionEnergy_le_formBound z u).trans_lt
    apply ENNReal.mul_lt_top
    · apply ENNReal.sum_lt_top.mpr
      intro _ _
      exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.coe_lt_top
    · exact ENNReal.add_lt_top.mpr ⟨hm, ENNReal.mul_lt_top (by norm_num) he⟩

end LiebThirring

end
