/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumState
public import LiebThirring.Kinetic.CurryingProductBasic
import LiebThirring.Kinetic.DensityBasic

/-! # Joint probability and one-body cluster measures

The one-body measures sum coordinate pushforwards of the joint probability.
This construction permits arbitrary electron–nuclear correlations. Their
masses are the particle counts times the squared L² norm.
Lieb–Lebowitz (1972) II.E before (2.25).
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

/-- Joint spatial probability, with the spin basis already summed by its L² norm. -/
@[expose] noncomputable def quantumProbabilityMeasure {N M q : ℕ}
    (ψ : QuantumState N M q) : Measure (QuantumConfiguration N M) :=
  volume.withDensity (fun X => ‖ψ X‖ₑ ^ 2)

theorem quantumProbabilityMeasure_mass {N M q : ℕ} (ψ : QuantumState N M q) :
    quantumProbabilityMeasure ψ Set.univ = ‖ψ‖ₑ ^ 2 := by
  rw [quantumProbabilityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_l2_enorm_sq]

instance quantumProbabilityMeasure_isFiniteMeasure {N M q : ℕ} (ψ : QuantumState N M q) :
    IsFiniteMeasure (quantumProbabilityMeasure ψ) where
  measure_univ_lt_top := by
    rw [quantumProbabilityMeasure_mass]
    exact ENNReal.pow_lt_top (by simp [enorm_eq_nnnorm])

/-- Testing the joint probability is the actual squared-amplitude expectation. -/
theorem quantumProbabilityMeasure_lintegral {N M q : ℕ}
    (ψ : QuantumState N M q) (w : QuantumConfiguration N M → ℝ≥0∞)
    (hw : Measurable w) :
    (∫⁻ X, w X ∂quantumProbabilityMeasure ψ) =
      ∫⁻ X, w X * ‖ψ X‖ₑ ^ 2 := by
  unfold quantumProbabilityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    ((Lp.aestronglyMeasurable ψ).enorm.pow_const 2) hw.aemeasurable]
  exact lintegral_congr (fun X => mul_comm _ _)

/-- Uncharged electronic one-body number measure. -/
@[expose] noncomputable def quantumElectronMeasure {N M q : ℕ}
    (ψ : QuantumState N M q) : Measure Position :=
  ∑ i : Fin N, (quantumProbabilityMeasure ψ).map (fun X => particlePosition X.fst i)

/-- Uncharged nuclear one-body number measure. -/
@[expose] noncomputable def quantumNuclearMeasure {N M q : ℕ}
    (ψ : QuantumState N M q) : Measure Position :=
  ∑ k : Fin M, (quantumProbabilityMeasure ψ).map (fun X => particlePosition X.snd k)

instance quantumElectronMeasure_isFiniteMeasure {N M q : ℕ} (ψ : QuantumState N M q) :
    IsFiniteMeasure (quantumElectronMeasure ψ) := by
  unfold quantumElectronMeasure
  infer_instance

instance quantumNuclearMeasure_isFiniteMeasure {N M q : ℕ} (ψ : QuantumState N M q) :
    IsFiniteMeasure (quantumNuclearMeasure ψ) := by
  unfold quantumNuclearMeasure
  infer_instance

theorem quantumElectronMeasure_mass {N M q : ℕ} (ψ : QuantumState N M q) :
    quantumElectronMeasure ψ Set.univ = (N : ℝ≥0∞) * ‖ψ‖ₑ ^ 2 := by
  have hm (i : Fin N) : Measurable (fun X : QuantumConfiguration N M =>
      particlePosition X.fst i) :=
    (measurable_particlePosition i).comp
      (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  simp [quantumElectronMeasure, Measure.map_apply (hm _), quantumProbabilityMeasure_mass]

theorem quantumNuclearMeasure_mass {N M q : ℕ} (ψ : QuantumState N M q) :
    quantumNuclearMeasure ψ Set.univ = (M : ℝ≥0∞) * ‖ψ‖ₑ ^ 2 := by
  have hm (k : Fin M) : Measurable (fun X : QuantumConfiguration N M =>
      particlePosition X.snd k) :=
    (measurable_particlePosition k).comp
      (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  simp [quantumNuclearMeasure, Measure.map_apply (hm _), quantumProbabilityMeasure_mass]

theorem quantumElectronMeasure_mass_of_normalized {N M q : ℕ}
    (ψ : QuantumState N M q) (hψ : ‖ψ‖ = 1) :
    quantumElectronMeasure ψ Set.univ = N := by
  rw [quantumElectronMeasure_mass, ← ofReal_norm, hψ]
  simp

theorem quantumNuclearMeasure_mass_of_normalized {N M q : ℕ}
    (ψ : QuantumState N M q) (hψ : ‖ψ‖ = 1) :
    quantumNuclearMeasure ψ Set.univ = M := by
  rw [quantumNuclearMeasure_mass, ← ofReal_norm, hψ]
  simp

/-- Electronic one-body testing counts each particle, without independence assumptions. -/
theorem quantumElectronMeasure_lintegral {N M q : ℕ}
    (ψ : QuantumState N M q) (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂quantumElectronMeasure ψ) =
      ∑ i : Fin N, ∫⁻ X, w (particlePosition X.fst i) * ‖ψ X‖ₑ ^ 2 := by
  unfold quantumElectronMeasure
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun X : QuantumConfiguration N M => particlePosition X.fst i) :=
    (measurable_particlePosition i).comp
      (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  rw [lintegral_map hw hm]
  exact quantumProbabilityMeasure_lintegral ψ _ (hw.comp hm)

/-- Nuclear one-body testing counts each particle, without independence assumptions. -/
theorem quantumNuclearMeasure_lintegral {N M q : ℕ}
    (ψ : QuantumState N M q) (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂quantumNuclearMeasure ψ) =
      ∑ k : Fin M, ∫⁻ X, w (particlePosition X.snd k) * ‖ψ X‖ₑ ^ 2 := by
  unfold quantumNuclearMeasure
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro k _
  have hm : Measurable (fun X : QuantumConfiguration N M => particlePosition X.snd k) :=
    (measurable_particlePosition k).comp
      (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  rw [lintegral_map hw hm]
  exact quantumProbabilityMeasure_lintegral ψ _ (hw.comp hm)

end LiebThirring
end
