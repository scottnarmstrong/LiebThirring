/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Permutations
public import LiebThirring.ThermoClusters.Marginals

/-! # Label permutation invariance of the one-body number measures

Spatial probability is pulled back by the joint label permutation, while
spin permutation is an isometry. Summing coordinate marginals removes the
label permutation. These identities justify iterated finite cluster assembly.

-/

public section
open MeasureTheory WithLp
open scoped ENNReal
namespace LiebThirring

/-- A particle permutation transports actual joint probability by its inverse spatial map. -/
theorem quantumProbabilityMeasure_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumProbabilityMeasure (quantumStatePermutation σ τ ψ) =
      (quantumProbabilityMeasure ψ).map (quantumPermutation σ τ).symm := by
  apply Measure.ext_of_lintegral
  intro w hw
  rw [lintegral_map hw (quantumPermutation σ τ).symm.continuous.measurable]
  rw [quantumProbabilityMeasure_lintegral _ w hw]
  have hr := quantumProbabilityMeasure_lintegral ψ
    (fun Y => w ((quantumPermutation σ τ).symm Y))
    (hw.comp (quantumPermutation σ τ).symm.continuous.measurable)
  rw [hr]
  calc
    _ = ∫⁻ X, w X * ‖ψ (quantumPermutation σ τ X)‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_quantumStatePermutation σ τ ψ] with X hX
      rw [hX, LinearIsometryEquiv.enorm_map]
    _ = ∫⁻ X, w ((quantumPermutation σ τ).symm (quantumPermutation σ τ X)) *
        ‖ψ (quantumPermutation σ τ X)‖ₑ ^ 2 := by
      simp only [LinearIsometryEquiv.symm_apply_apply]
    _ = _ := (quantumPermutation σ τ).measurePreserving.lintegral_comp_emb
      (quantumPermutation σ τ).toHomeomorph.measurableEmbedding
      (fun Y => w ((quantumPermutation σ τ).symm Y) * ‖ψ Y‖ₑ ^ 2)

/-- Electronic one-body number measure is invariant under both joint label permutations. -/
theorem quantumElectronMeasure_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumElectronMeasure (quantumStatePermutation σ τ ψ) = quantumElectronMeasure ψ := by
  classical
  unfold quantumElectronMeasure
  rw [quantumProbabilityMeasure_quantumStatePermutation]
  have hm (i : Fin N) : Measurable (fun X : QuantumConfiguration N M => particlePosition X.fst i) :=
    (measurable_particlePosition i).comp
      (WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  simp only [Measure.map_map (hm _) (quantumPermutation σ τ).symm.continuous.measurable]
  have hp (X : QuantumConfiguration N M) (i : Fin N) :
      particlePosition ((quantumPermutation σ τ).symm X).fst i =
        particlePosition X.fst (σ.symm i) := by
    simpa using (particlePosition_quantumPermutation_fst σ τ
      ((quantumPermutation σ τ).symm X) (σ.symm i)).symm
  simp only [Function.comp_def, hp]
  change (∑ i : Fin N, (quantumProbabilityMeasure ψ).map
    (fun X => particlePosition X.fst (σ.symm i))) = _
  exact Equiv.sum_comp σ.symm (fun i =>
    (quantumProbabilityMeasure ψ).map (fun X => particlePosition X.fst i))

/-- Nuclear one-body number measure is invariant under both joint label permutations. -/
theorem quantumNuclearMeasure_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumNuclearMeasure (quantumStatePermutation σ τ ψ) = quantumNuclearMeasure ψ := by
  classical
  unfold quantumNuclearMeasure
  rw [quantumProbabilityMeasure_quantumStatePermutation]
  have hm (k : Fin M) : Measurable (fun X : QuantumConfiguration N M => particlePosition X.snd k) :=
    (measurable_particlePosition k).comp
      (WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable
  simp only [Measure.map_map (hm _) (quantumPermutation σ τ).symm.continuous.measurable]
  have hp (X : QuantumConfiguration N M) (k : Fin M) :
      particlePosition ((quantumPermutation σ τ).symm X).snd k =
        particlePosition X.snd (τ.symm k) := by
    simpa using (particlePosition_quantumPermutation_snd σ τ
      ((quantumPermutation σ τ).symm X) (τ.symm k)).symm
  simp only [Function.comp_def, hp]
  change (∑ k : Fin M, (quantumProbabilityMeasure ψ).map
    (fun X => particlePosition X.snd (τ.symm k))) = _
  exact Equiv.sum_comp τ.symm (fun k =>
    (quantumProbabilityMeasure ψ).map (fun X => particlePosition X.snd k))

end LiebThirring
end
