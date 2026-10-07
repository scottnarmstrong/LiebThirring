/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.TensorExpectations
import LiebThirring.Kinetic.DensityBasic

/-! # Additive one-body marginals of normalized ordered clusters

The spectator cluster contributes mass one. Therefore each one-body number
measure of the product is the sum of the corresponding cluster measures.

-/

public section
open MeasureTheory WithLp
open scoped ENNReal SchwartzMap
namespace LiebThirring

/-- A coordinate belonging to the first cluster has its original probability marginal. -/
theorem clusterProductSchwartz_coordinateMeasure_left {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (a : QuantumConfiguration n₁ m₁ → Position) (ha : Measurable a)
    (hn : ‖h.toLp 2 volume‖ = 1) :
    (quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)).map
      (fun X => a (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst) =
      (quantumProbabilityMeasure (f.toLp 2 volume)).map a := by
  apply Measure.ext_of_lintegral
  intro w hw
  have hm : Measurable (fun X : QuantumConfiguration (n₁+n₂) (m₁+m₂) =>
      a (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst) :=
    ha.comp ((WithLp.fstL 2 ℝ _ _).continuous.measurable.comp
      (quantumClusterSplit n₁ n₂ m₁ m₂).continuous.measurable)
  rw [lintegral_map hw hm, lintegral_map hw ha]
  have he := clusterProductSchwartz_expectation_left f h hf hh (fun Y => w (a Y)) (hw.comp ha)
  have hn' : ‖h.toLp 2 volume‖ₑ ^ 2 = 1 := by rw [← ofReal_norm, hn]; norm_num
  simpa only [hn', mul_one] using he

/-- A coordinate belonging to the second cluster has its original probability marginal. -/
theorem clusterProductSchwartz_coordinateMeasure_right {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (a : QuantumConfiguration n₂ m₂ → Position) (ha : Measurable a)
    (hn : ‖f.toLp 2 volume‖ = 1) :
    (quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)).map
      (fun X => a (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd) =
      (quantumProbabilityMeasure (h.toLp 2 volume)).map a := by
  apply Measure.ext_of_lintegral
  intro w hw
  have hm : Measurable (fun X : QuantumConfiguration (n₁+n₂) (m₁+m₂) =>
      a (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd) :=
    ha.comp ((WithLp.sndL 2 ℝ _ _).continuous.measurable.comp
      (quantumClusterSplit n₁ n₂ m₁ m₂).continuous.measurable)
  rw [lintegral_map hw hm, lintegral_map hw ha]
  have he := clusterProductSchwartz_expectation_right f h hf hh (fun Y => w (a Y)) (hw.comp ha)
  have hn' : ‖f.toLp 2 volume‖ₑ ^ 2 = 1 := by rw [← ofReal_norm, hn]; norm_num
  simpa only [hn', one_mul] using he

/-- Electronic number measures add for normalized ordered joint clusters. -/
theorem quantumElectronMeasure_clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumElectronMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumElectronMeasure (f.toLp 2 volume) + quantumElectronMeasure (h.toLp 2 volume) := by
  classical
  unfold quantumElectronMeasure
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact clusterProductSchwartz_coordinateMeasure_left f h hf hh
      (fun X => particlePosition X.fst i)
      ((measurable_particlePosition i).comp
        (WithLp.fstL 2 ℝ (Configuration n₁) (Configuration m₁)).continuous.measurable) hnh
  · apply Finset.sum_congr rfl
    intro i _
    exact clusterProductSchwartz_coordinateMeasure_right f h hf hh
      (fun X => particlePosition X.fst i)
      ((measurable_particlePosition i).comp
        (WithLp.fstL 2 ℝ (Configuration n₂) (Configuration m₂)).continuous.measurable) hnf

/-- Nuclear number measures add for normalized ordered joint clusters. -/
theorem quantumNuclearMeasure_clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumNuclearMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumNuclearMeasure (f.toLp 2 volume) + quantumNuclearMeasure (h.toLp 2 volume) := by
  classical
  unfold quantumNuclearMeasure
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact clusterProductSchwartz_coordinateMeasure_left f h hf hh
      (fun X => particlePosition X.snd i)
      ((measurable_particlePosition i).comp
        (WithLp.sndL 2 ℝ (Configuration n₁) (Configuration m₁)).continuous.measurable) hnh
  · apply Finset.sum_congr rfl
    intro i _
    exact clusterProductSchwartz_coordinateMeasure_right f h hf hh
      (fun X => particlePosition X.snd i)
      ((measurable_particlePosition i).comp
        (WithLp.sndL 2 ℝ (Configuration n₂) (Configuration m₂)).continuous.measurable) hnf

end LiebThirring
end
