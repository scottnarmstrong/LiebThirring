/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.Fibres
public import LiebThirring.Thermodynamic.QuantumRepulsionEnergy
public import LiebThirring.Thermodynamic.QuantumAttractionEnergy
import LiebThirring.Assembly.Coulomb
import LiebThirring.Kinetic.DensityBasic

/-! # Fibrewise Coulomb expectations for the quantum stability -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.ThermoStability

theorem measurable_jointAttraction (N M z : ℕ) :
    Measurable (fun X : QuantumConfiguration N M =>
      attraction (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition X.snd k) X.fst) := by
  unfold attraction
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact measurable_const.mul (((measurable_particlePosition i).comp
    (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable).sub
      ((measurable_particlePosition k).comp
        (continuous_snd.comp (WithLp.prod_continuous_ofLp ..)).measurable)).norm.ennreal_ofReal.inv

theorem measurable_jointNuclearRepulsion (N M z : ℕ) :
    Measurable (fun X : QuantumConfiguration N M =>
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k)) := by
  unfold nuclearRepulsion
  refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
  exact measurable_const.mul (((measurable_particlePosition k).comp
    (continuous_snd.comp (WithLp.prod_continuous_ofLp ..)).measurable).sub
      ((measurable_particlePosition l).comp
        (continuous_snd.comp (WithLp.prod_continuous_ofLp ..)).measurable)).norm.ennreal_ofReal.inv

theorem quantumAttractionEnergy_eq_fibre_lintegral {N M q : ℕ}
    (z : ℕ) (ψ : QuantumState N M q) :
    quantumAttractionEnergy z ψ = ∫⁻ R : Configuration M, ∫⁻ x : Configuration N,
      attraction (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) x *
        (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2 :=
  lintegral_weight_electronFibreField ψ _ (measurable_jointAttraction N M z)

theorem quantumRepulsionEnergy_eq_fibre_lintegral {N M q : ℕ}
    (z : ℕ) (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z ψ = ∫⁻ R : Configuration M,
      (∫⁻ x : Configuration N, electronRepulsion x *
        (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2) +
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition R k) * (‖electronFibreField ψ R‖₊ : ℝ≥0∞) ^ 2 := by
  have hw : Measurable (fun X : QuantumConfiguration N M =>
      electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k)) :=
    (Assembly.measurable_electronRepulsion.comp
      (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable).add
        (measurable_jointNuclearRepulsion N M z)
  change (∫⁻ X : QuantumConfiguration N M,
    (electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition X.snd k)) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) = _
  rw [lintegral_weight_electronFibreField ψ _ hw]
  apply lintegral_congr
  intro R
  change (∫⁻ x : Configuration N,
    (electronRepulsion x + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition R k)) * (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2) = _
  simp only [add_mul]
  have hm : Measurable (fun x : Configuration N => electronRepulsion x *
      (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2) :=
    Assembly.measurable_electronRepulsion.mul
      ((Lp.stronglyMeasurable (electronFibreField ψ R)).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
  rw [lintegral_add_left hm,
    lintegral_const_mul _ ((Lp.stronglyMeasurable (electronFibreField ψ R)).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)]
  congr 1
  change _ * (∫⁻ x, ‖electronFibreField ψ R x‖ₑ ^ 2) = _
  rw [lintegral_l2_enorm_sq]
  rfl

end LiebThirring.ThermoStability

end
