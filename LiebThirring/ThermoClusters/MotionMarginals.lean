/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.StateMotion
public import LiebThirring.ThermoClusters.Marginals
import LiebThirring.Kinetic.DensityBasic

/-! # Rigid covariance of actual cluster number measures

Both particle species are pushed forward by the same spatial rigid motion.
No factorization, smoothness, statistics or normalization assumption is
required. These are the actual marginals used in the cluster cross formula.
direct change of variables, direct proof.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal
namespace LiebThirring

/-- Actual spatial probability is pushed forward by the joint rigid motion. -/
theorem quantumProbabilityMeasure_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumProbabilityMeasure (quantumStateMotion Q c ψ) =
      (quantumProbabilityMeasure ψ).map (quantumRigidMotion Q c) := by
  apply Measure.ext_of_lintegral
  intro w hw
  rw [lintegral_map hw (quantumRigidMotion Q c).continuous.measurable]
  rw [quantumProbabilityMeasure_lintegral _ w hw]
  rw [quantumProbabilityMeasure_lintegral ψ (fun X => w (quantumRigidMotion Q c X))
    (hw.comp (quantumRigidMotion Q c).continuous.measurable)]
  calc
    _ = ∫⁻ X, w X * ‖ψ ((quantumRigidMotion Q c).symm X)‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_quantumStateMotion Q c ψ] with X hX
      rw [hX]
      rfl
    _ = ∫⁻ X, w (quantumRigidMotion Q c ((quantumRigidMotion Q c).symm X)) *
        ‖ψ ((quantumRigidMotion Q c).symm X)‖ₑ ^ 2 := by
      simp only [AffineIsometryEquiv.apply_symm_apply]
    _ = _ := (measurePreserving_quantumRigidMotion_symm Q c).lintegral_comp_emb
      (quantumRigidMotion Q c).toHomeomorph.symm.measurableEmbedding
      (fun Y => w (quantumRigidMotion Q c Y) * ‖ψ Y‖ₑ ^ 2)

/-- Actual electron number measure transforms by spatial pushforward. -/
theorem quantumElectronMeasure_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumElectronMeasure (quantumStateMotion Q c ψ) =
      (quantumElectronMeasure ψ).map (spatialRigidMotion Q c) := by
  classical
  have hm (i : Fin N) : Measurable (fun X : QuantumConfiguration N M => particlePosition X.fst i) :=
    (measurable_particlePosition i).comp
      (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  unfold quantumElectronMeasure
  rw [quantumProbabilityMeasure_quantumStateMotion,
    Measure.map_finset_sum (spatialRigidMotion Q c).continuous.measurable.aemeasurable]
  simp only [Measure.map_map (hm _) (quantumRigidMotion Q c).continuous.measurable,
    Measure.map_map (spatialRigidMotion Q c).continuous.measurable (hm _)]
  rfl

/-- Actual nuclear number measure transforms by spatial pushforward. -/
theorem quantumNuclearMeasure_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumNuclearMeasure (quantumStateMotion Q c ψ) =
      (quantumNuclearMeasure ψ).map (spatialRigidMotion Q c) := by
  classical
  have hm (k : Fin M) : Measurable (fun X : QuantumConfiguration N M => particlePosition X.snd k) :=
    (measurable_particlePosition k).comp
      (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  unfold quantumNuclearMeasure
  rw [quantumProbabilityMeasure_quantumStateMotion,
    Measure.map_finset_sum (spatialRigidMotion Q c).continuous.measurable.aemeasurable]
  simp only [Measure.map_map (hm _) (quantumRigidMotion Q c).continuous.measurable,
    Measure.map_map (spatialRigidMotion Q c).continuous.measurable (hm _)]
  rfl

end LiebThirring
end
