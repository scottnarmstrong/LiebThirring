/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor
public import LiebThirring.Thermodynamic.QuantumElectronKineticEnergy
public import LiebThirring.Thermodynamic.QuantumNuclearKineticEnergy
import LiebThirring.Fourier.Functoriality
import LiebThirring.Fourier.Schwartz
import LiebThirring.Kinetic.CurryingProductBasic

/-! # Kinetic energies of products of correlated clusters

The electronic and nuclear Fourier energies factor over the
ordered cluster tensor. Each cluster may correlate all its electronic and
nuclear coordinates. The unnormalized formulas retain the spectator L² mass;
normalized clusters give exact additivity, including vacuum sectors.

The proof factors the Fourier transform spin coordinate by spin coordinate,
uses the volume-preserving joint split, and applies Plancherel to the
spectator mass. Proof: cluster assembly; Lieb–Lebowitz (1972) II.E before (2.25).
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform
namespace LiebThirring
private theorem split_inner {n₁ n₂ m₁ m₂ : ℕ}
    (P : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂)
    (ξ : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    inner ℝ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P) ξ =
      inner ℝ P.1 (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).fst +
      inner ℝ P.2 (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).snd := by
  rw [← (quantumClusterSplit n₁ n₂ m₁ m₂).inner_map_map]
  have he : quantumClusterSplit n₁ n₂ m₁ m₂
      ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P) = toLp 2 P := by
    exact (quantumClusterSplit n₁ n₂ m₁ m₂).apply_symm_apply _
  rw [he, WithLp.prod_inner_apply]
  rfl

private theorem fourier_scalar_product {n₁ n₂ m₁ m₂ : ℕ}
    (f : QuantumConfiguration n₁ m₁ → ℂ) (h : QuantumConfiguration n₂ m₂ → ℂ)
    (ξ : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    (𝓕 (fun X => f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst *
      h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd)) ξ =
    (𝓕 f) (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).fst *
      (𝓕 h) (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).snd := by
  rw [Real.fourier_eq]
  rw [← ((measurePreserving_quantumClusterSplit n₁ n₂ m₁ m₂).symm
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).toMeasurableEquiv).integral_comp
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm.toMeasurableEquiv.measurableEmbedding]
  have heq : (fun P : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
    Real.fourierChar (-inner ℝ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P) ξ) •
      (f (quantumClusterSplit n₁ n₂ m₁ m₂ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P)).fst *
       h (quantumClusterSplit n₁ n₂ m₁ m₂ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P)).snd)) =
    (fun P : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      (Real.fourierChar (-inner ℝ P.1 (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).fst) • f P.1) *
      (Real.fourierChar (-inner ℝ P.2 (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).snd) • h P.2)) := by
    funext P
    rw [split_inner]
    have he : quantumClusterSplit n₁ n₂ m₁ m₂
        ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P) = toLp 2 P :=
      (quantumClusterSplit n₁ n₂ m₁ m₂).apply_symm_apply _
    rw [he]
    simp only [WithLp.fst, WithLp.snd, neg_add,
      Real.fourierChar.map_add_eq_mul, Circle.smul_def, Circle.coe_mul, smul_eq_mul]
    ring
  change (∫ P, Real.fourierChar (-inner ℝ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P) ξ) •
    (f (quantumClusterSplit n₁ n₂ m₁ m₂ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P)).fst *
    h (quantumClusterSplit n₁ n₂ m₁ m₂ ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).symm P)).snd) ∂volume.prod volume) = _
  rw [heq]
  exact integral_prod_mul
    (fun X : QuantumConfiguration n₁ m₁ =>
      Real.fourierChar (-inner ℝ X (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).fst) • f X)
    (fun Y : QuantumConfiguration n₂ m₂ =>
      Real.fourierChar (-inner ℝ Y (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).snd) • h Y)

private theorem fourier_spin_apply {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (ξ : QuantumConfiguration N M)
    (s : SpinLabels N q) :
    ((𝓕 f) ξ) s = (𝓕 (fun X => f X s)) ξ := by
  have he := Fourier.fourier_postcomp (PiLp.proj 2 (𝕜 := ℂ)
    (fun _ : SpinLabels N q => ℂ) s) f
  exact (congrArg (fun g : 𝓢(QuantumConfiguration N M, ℂ) => g ξ) he).symm

/-- The Fourier transform of an ordered correlated cluster product factors with the same coordinate and spin split. -/
theorem fourier_clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (ξ : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    (𝓕 (clusterProductSchwartz f h hf hh)) ξ = clusterProduct (fun X => (𝓕 f) X) (fun X => (𝓕 h) X) ξ := by
  ext s
  rw [fourier_spin_apply]
  change (𝓕 (fun X => f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst
    ((clusterSpinEquiv n₁ n₂ q).symm s).1 * h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd
    ((clusterSpinEquiv n₁ n₂ q).symm s).2)) ξ = _
  rw [fourier_scalar_product (fun X => f X ((clusterSpinEquiv n₁ n₂ q).symm s).1)
    (fun X => h X ((clusterSpinEquiv n₁ n₂ q).symm s).2) ξ]
  change _ = ((𝓕 f) (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).fst)
    ((clusterSpinEquiv n₁ n₂ q).symm s).1 *
    ((𝓕 h) (quantumClusterSplit n₁ n₂ m₁ m₂ ξ).snd)
    ((clusterSpinEquiv n₁ n₂ q).symm s).2
  rw [fourier_spin_apply, fourier_spin_apply]

private theorem configurationClusterSplit_nnnorm_sq (n k : ℕ) (x : Configuration (n+k)) :
    (‖x‖₊ : ℝ≥0∞)^2 =
      (‖(configurationClusterSplit n k x).fst‖₊ : ℝ≥0∞)^2 +
      (‖(configurationClusterSplit n k x).snd‖₊ : ℝ≥0∞)^2 := by
  have hr : ‖x‖^2 = ‖(configurationClusterSplit n k x).fst‖^2 +
      ‖(configurationClusterSplit n k x).snd‖^2 := by
    rw [← WithLp.prod_norm_sq_eq_of_L2, (configurationClusterSplit n k).norm_map]
  have he := congrArg ENNReal.ofReal hr
  simpa only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm] using he

private theorem clusterProduct_lintegral_sum_weight {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (w₁ : QuantumConfiguration n₁ m₁ → ℝ≥0∞) (hw₁ : Measurable w₁)
    (w₂ : QuantumConfiguration n₂ m₂ → ℝ≥0∞) (hw₂ : Measurable w₂) :
    (∫⁻ X, (w₁ (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst +
      w₂ (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd) *
      (‖clusterProduct (fun X => f X) (fun X => h X) X‖₊ : ℝ≥0∞)^2) =
    (∫⁻ X, w₁ X * (‖f X‖₊ : ℝ≥0∞)^2) * (∫⁻ Y, (‖h Y‖₊ : ℝ≥0∞)^2) +
    (∫⁻ X, (‖f X‖₊ : ℝ≥0∞)^2) * (∫⁻ Y, w₂ Y * (‖h Y‖₊ : ℝ≥0∞)^2) := by
  have h₁ := clusterProduct_lintegral_weight (fun X => f X) f.continuous.measurable
    (fun X => h X) h.continuous.measurable w₁ hw₁ (fun _ => 1) measurable_const
  have h₂ := clusterProduct_lintegral_weight (fun X => f X) f.continuous.measurable
    (fun X => h X) h.continuous.measurable (fun _ => 1) measurable_const w₂ hw₂
  simp only [mul_one, one_mul] at h₁ h₂
  simp_rw [add_mul]
  rw [lintegral_add_left, h₁, h₂]
  exact (hw₁.comp ((WithLp.fstL 2 ℝ _ _).continuous.measurable.comp
    (quantumClusterSplit n₁ n₂ m₁ m₂).continuous.measurable)).mul
    ((contDiff_clusterProduct (fun X => f X) (fun X => h X)
      (f.smooth ⊤) (h.smooth ⊤)).continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)

private theorem schwartz_fourier_mass {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (∫⁻ X, (‖(𝓕 f) X‖₊ : ℝ≥0∞)^2) = (‖f.toLp 2 volume‖₊ : ℝ≥0∞)^2 := by
  rw [Fourier.lintegral_norm_sq_fourier]
  calc
    _ = ∫⁻ X, ‖(f.toLp 2 volume) X‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume] with X hX
      rw [hX, enorm_eq_nnnorm]
    _ = _ := by simpa only [enorm_eq_nnnorm] using lintegral_l2_enorm_sq (f.toLp 2 volume)

private noncomputable def electronWeight {N M : ℕ} (X : QuantumConfiguration N M) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)^2) * (‖X.fst‖₊ : ℝ≥0∞)^2
private noncomputable def nuclearWeight {N M : ℕ} (X : QuantumConfiguration N M) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)^2) * (‖X.snd‖₊ : ℝ≥0∞)^2

private theorem electronWeight_measurable (N M : ℕ) :
    Measurable (electronWeight (N:=N) (M:=M)) := by
  unfold electronWeight
  fun_prop
private theorem nuclearWeight_measurable (N M : ℕ) :
    Measurable (nuclearWeight (N:=N) (M:=M)) := by
  unfold nuclearWeight
  fun_prop

private theorem electronWeight_split {n₁ n₂ m₁ m₂ : ℕ}
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    electronWeight X = electronWeight (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst +
      electronWeight (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd := by
  unfold electronWeight
  rw [configurationClusterSplit_nnnorm_sq n₁ n₂ X.fst, mul_add]
  rfl
private theorem nuclearWeight_split {n₁ n₂ m₁ m₂ : ℕ}
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    nuclearWeight X = nuclearWeight (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst +
      nuclearWeight (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd := by
  unfold nuclearWeight
  rw [configurationClusterSplit_nnnorm_sq m₁ m₂ X.snd, mul_add]
  rfl

private theorem electronEnergy_fourier {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumElectronKineticEnergy (f.toLp 2 volume) =
      ∫⁻ X, electronWeight X * (‖(𝓕 f) X‖₊ : ℝ≥0∞)^2 := by
  unfold quantumElectronKineticEnergy
  change (∫⁻ X, electronWeight X * (‖(𝓕 (f.toLp 2 volume) : QuantumState N M q) X‖₊ : ℝ≥0∞)^2) = _
  rw [SchwartzMap.toLp_fourier_eq]
  apply lintegral_congr_ae
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with X hX
  rw [hX]
private theorem nuclearEnergy_fourier {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumNuclearKineticEnergy (f.toLp 2 volume) =
      ∫⁻ X, nuclearWeight X * (‖(𝓕 f) X‖₊ : ℝ≥0∞)^2 := by
  unfold quantumNuclearKineticEnergy
  change (∫⁻ X, nuclearWeight X * (‖(𝓕 (f.toLp 2 volume) : QuantumState N M q) X‖₊ : ℝ≥0∞)^2) = _
  rw [SchwartzMap.toLp_fourier_eq]
  apply lintegral_congr_ae
  filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with X hX
  rw [hX]

/-- The electron kinetic energy of two smooth correlated clusters has the exact spectator masses. -/
theorem quantumElectronKineticEnergy_clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X)) :
    quantumElectronKineticEnergy ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumElectronKineticEnergy (f.toLp 2 volume) * (‖h.toLp 2 volume‖₊ : ℝ≥0∞)^2 +
      (‖f.toLp 2 volume‖₊ : ℝ≥0∞)^2 * quantumElectronKineticEnergy (h.toLp 2 volume) := by
  rw [electronEnergy_fourier]
  simp_rw [fourier_clusterProductSchwartz, electronWeight_split]
  rw [clusterProduct_lintegral_sum_weight (𝓕 f) (𝓕 h) electronWeight
    (electronWeight_measurable _ _) electronWeight (electronWeight_measurable _ _),
    schwartz_fourier_mass, schwartz_fourier_mass, ← electronEnergy_fourier,
    ← electronEnergy_fourier]

/-- The nuclear kinetic energy has the same exact spectator-mass formula. -/
theorem quantumNuclearKineticEnergy_clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X)) :
    quantumNuclearKineticEnergy ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumNuclearKineticEnergy (f.toLp 2 volume) * (‖h.toLp 2 volume‖₊ : ℝ≥0∞)^2 +
      (‖f.toLp 2 volume‖₊ : ℝ≥0∞)^2 * quantumNuclearKineticEnergy (h.toLp 2 volume) := by
  rw [nuclearEnergy_fourier]
  simp_rw [fourier_clusterProductSchwartz, nuclearWeight_split]
  rw [clusterProduct_lintegral_sum_weight (𝓕 f) (𝓕 h) nuclearWeight
    (nuclearWeight_measurable _ _) nuclearWeight (nuclearWeight_measurable _ _),
    schwartz_fourier_mass, schwartz_fourier_mass, ← nuclearEnergy_fourier,
    ← nuclearEnergy_fourier]


/-- Normalized correlated clusters have additive electron kinetic energy. -/
theorem quantumElectronKineticEnergy_clusterProductSchwartz_of_normalized {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumElectronKineticEnergy ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumElectronKineticEnergy (f.toLp 2 volume) +
      quantumElectronKineticEnergy (h.toLp 2 volume) := by
  have hnf' : (‖f.toLp 2 volume‖₊ : ℝ≥0∞) = 1 := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, hnf, ENNReal.ofReal_one]
  have hnh' : (‖h.toLp 2 volume‖₊ : ℝ≥0∞) = 1 := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, hnh, ENNReal.ofReal_one]
  rw [quantumElectronKineticEnergy_clusterProductSchwartz, hnf', hnh', one_pow,
    mul_one, one_mul]

/-- Normalized correlated clusters have additive nuclear kinetic energy. -/
theorem quantumNuclearKineticEnergy_clusterProductSchwartz_of_normalized {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumNuclearKineticEnergy ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumNuclearKineticEnergy (f.toLp 2 volume) +
      quantumNuclearKineticEnergy (h.toLp 2 volume) := by
  have hnf' : (‖f.toLp 2 volume‖₊ : ℝ≥0∞) = 1 := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, hnf, ENNReal.ofReal_one]
  have hnh' : (‖h.toLp 2 volume‖₊ : ℝ≥0∞) = 1 := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, hnh, ENNReal.ofReal_one]
  rw [quantumNuclearKineticEnergy_clusterProductSchwartz, hnf', hnh', one_pow,
    mul_one, one_mul]

end LiebThirring

end
