/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ShuffleSupport
public import LiebThirring.ThermoClusters.PermutationMarginals
public import LiebThirring.ThermoClusters.TensorMarginals
import LiebThirring.ThermoClusters.DisjointSum
import LiebThirring.Variational.TrialScaling

/-! # One-body number measures of the actual binary assembly

The two number measures of the genuine double-quotient binary assembly equal
those of the ordered product. The proof tests an arbitrary measurable
position observable, sums it over the relevant species, and uses the actual
disjoint closed supports supplied by source confinement in disjoint regions.
Signs and label permutations preserve each term's number measure, and the
reciprocal square-root cardinal factor cancels the sum of the equal tests.

Normalized inputs therefore give the sum of their electron number measures
and the sum of their nuclear number measures, without any independence
assumption inside either correlated cluster. Source: thermodynamic cluster assembly.
-/

public section

open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring
private noncomputable def electronWeight {N M : ℕ} (w : Position → ℝ≥0∞)
    (X : QuantumConfiguration N M) : ℝ≥0∞ := ∑ i : Fin N, w (particlePosition X.fst i)
private noncomputable def nuclearWeight {N M : ℕ} (w : Position → ℝ≥0∞)
    (X : QuantumConfiguration N M) : ℝ≥0∞ := ∑ k : Fin M, w (particlePosition X.snd k)
private theorem electronWeight_measurable {N M : ℕ} (w : Position → ℝ≥0∞) (hw : Measurable w) :
    Measurable (electronWeight (N:=N) (M:=M) w) := by
  classical
  unfold electronWeight
  apply Finset.measurable_sum
  intro i _
  exact hw.comp ((measurable_particlePosition i).comp (WithLp.fstL 2 ℝ _ _).continuous.measurable)
private theorem nuclearWeight_measurable {N M : ℕ} (w : Position → ℝ≥0∞) (hw : Measurable w) :
    Measurable (nuclearWeight (N:=N) (M:=M) w) := by
  classical
  unfold nuclearWeight
  apply Finset.measurable_sum
  intro k _
  exact hw.comp ((measurable_particlePosition k).comp (WithLp.sndL 2 ℝ _ _).continuous.measurable)
private theorem electron_measure_testing {N M q : ℕ} (ψ : QuantumState N M q)
    (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂quantumElectronMeasure ψ) =
      ∫⁻ X, electronWeight w X * (‖ψ X‖₊ : ℝ≥0∞)^2 := by
  classical
  rw [quantumElectronMeasure_lintegral ψ w hw]
  unfold electronWeight
  simp only [Finset.sum_mul, enorm_eq_nnnorm]
  rw [lintegral_finsetSum]
  intro i _
  exact (hw.comp ((measurable_particlePosition i).comp
    (WithLp.fstL 2 ℝ _ _).continuous.measurable)).mul
      ((Lp.stronglyMeasurable ψ).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
private theorem nuclear_measure_testing {N M q : ℕ} (ψ : QuantumState N M q)
    (w : Position → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂quantumNuclearMeasure ψ) =
      ∫⁻ X, nuclearWeight w X * (‖ψ X‖₊ : ℝ≥0∞)^2 := by
  classical
  rw [quantumNuclearMeasure_lintegral ψ w hw]
  unfold nuclearWeight
  simp only [Finset.sum_mul, enorm_eq_nnnorm]
  rw [lintegral_finsetSum]
  intro k _
  exact (hw.comp ((measurable_particlePosition k).comp
    (WithLp.sndL 2 ℝ _ _).continuous.measurable)).mul
      ((Lp.stronglyMeasurable ψ).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
private theorem probability_unit_smul {N M q : ℕ} (c : ℂ) (hc : ‖c‖=1)
    (ψ : QuantumState N M q) : quantumProbabilityMeasure (c • ψ) = quantumProbabilityMeasure ψ := by
  unfold quantumProbabilityMeasure
  apply withDensity_congr_ae
  filter_upwards [Lp.coeFn_smul c ψ] with X hX
  rw [hX, Pi.smul_apply, enorm_smul, ← ofReal_norm, hc, ENNReal.ofReal_one, one_mul]
private theorem electron_measure_unit_smul {N M q : ℕ} (c : ℂ) (hc : ‖c‖=1)
    (ψ : QuantumState N M q) : quantumElectronMeasure (c • ψ) = quantumElectronMeasure ψ := by
  unfold quantumElectronMeasure
  rw [probability_unit_smul c hc ψ]
private theorem nuclear_measure_unit_smul {N M q : ℕ} (c : ℂ) (hc : ‖c‖=1)
    (ψ : QuantumState N M q) : quantumNuclearMeasure (c • ψ) = quantumNuclearMeasure ψ := by
  unfold quantumNuclearMeasure
  rw [probability_unit_smul c hc ψ]
private theorem schwartz_toLp_complex_smul {N M q : ℕ} (c : ℂ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume).map_smul c f
private theorem schwartz_toLp_real_smul {N M q : ℕ} (c : ℝ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (c • f).toLp 2 volume = (c : ℂ) • f.toLp 2 volume := by
  change SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2 volume (c • f) = _
  rw [map_smul]
  exact RCLike.real_smul_eq_coe_smul c _
private theorem sign_norm_one {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : ‖((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
private theorem normalize_card_energy (k : ℕ) (hk : 0<k) (a : ℝ≥0∞) :
    (‖(Real.sqrt k)⁻¹‖₊ : ℝ≥0∞)^2 * ((k : ℝ≥0∞)*a) = a := by
  have hr : ‖(Real.sqrt k)⁻¹‖^2 * (k : ℝ) = 1 := by
    rw [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk.ne')
  have he := congrArg ENNReal.ofReal hr
  have hc : (‖(Real.sqrt k)⁻¹‖₊ : ℝ≥0∞)^2 * (k : ℝ≥0∞) = 1 := by
    simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, enorm_eq_nnnorm, ENNReal.ofReal_natCast, ENNReal.ofReal_one] using he
  rw [← mul_assoc, hc, one_mul]
private theorem schwartz_weight_toLp {N M q : ℕ}
    (p : QuantumConfiguration N M → ℝ≥0∞)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (∫⁻ X, p X * (‖f.toLp 2 volume X‖₊ : ℝ≥0∞)^2) =
      ∫⁻ X, p X * (‖f X‖₊ : ℝ≥0∞)^2 := by
  apply lintegral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with X hX
  rw [hX]
private theorem normalized_weight_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (hι : 0 < Fintype.card ι) (p : QuantumConfiguration N M → ℝ≥0∞) (hp : Measurable p)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (a : ℝ≥0∞) (he : ∀ i, (∫⁻ X, p X * (‖(f i).toLp 2 volume X‖₊ : ℝ≥0∞)^2) = a) :
    (∫⁻ X, p X * (‖((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2 volume X‖₊ : ℝ≥0∞)^2) = a := by
  classical
  rw [schwartz_toLp_real_smul, trial_lintegral_weight_smul,
    schwartz_weight_toLp, quantumSchwartz_lintegral_weight_sum p hp f hf]
  simp only [← schwartz_weight_toLp, he, Complex.nnnorm_real,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact normalize_card_energy _ hι a

variable {n₁ n₂ m₁ m₂ q : ℕ}
variable (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
  (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
  (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
  (hfa : quantum_antisymmetric (f.toLp 2 volume))
  (hha : quantum_antisymmetric (h.toLp 2 volume))
  (hfs : nuclear_symmetric (f.toLp 2 volume))
  (hhs : nuclear_symmetric (h.toLp 2 volume))

private theorem term_electronMeasure
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumElectronMeasure ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumElectronMeasure ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk, schwartz_toLp_complex_smul,
    electron_measure_unit_smul _ (sign_norm_one σ), quantumSchwartzPermutation_toLp,
    quantumElectronMeasure_quantumStatePermutation]

private theorem term_nuclearMeasure
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumNuclearMeasure ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumNuclearMeasure ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk, schwartz_toLp_complex_smul,
    nuclear_measure_unit_smul _ (sign_norm_one σ), quantumSchwartzPermutation_toLp,
    quantumNuclearMeasure_quantumStatePermutation]

variable (Ω₁ Ω₂ : Set Position)
  (hfp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₁)})
  (hhp : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₂)})
  (hΩ : Disjoint Ω₁ Ω₂)

include hfp hhp hΩ

/-- The actual binary shuffle assembly preserves the ordered product's electron number measure. -/
theorem quantumElectronMeasure_binaryClusterAssembly_eq_product :
    quantumElectronMeasure ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumElectronMeasure ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  apply Measure.ext_of_lintegral
  intro w hw
  rw [electron_measure_testing _ w hw, electron_measure_testing _ w hw]
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_weight_sum
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (electronWeight w) (electronWeight_measurable w hw)
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (∫⁻ X, electronWeight w X *
      (‖(clusterProductSchwartz f h hfc hhc).toLp 2 volume X‖₊ : ℝ≥0∞)^2)
    (fun p => by
      rw [← electron_measure_testing _ w hw, term_electronMeasure f h hfc hhc hfa hha hfs hhs p.1 p.2]
      exact electron_measure_testing _ w hw)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- Two normalized separated correlated inputs give the sum of their actual electron number measures. -/
theorem quantumElectronMeasure_binaryClusterAssembly
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumElectronMeasure ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumElectronMeasure (f.toLp 2 volume) + quantumElectronMeasure (h.toLp 2 volume) := by
  rw [quantumElectronMeasure_binaryClusterAssembly_eq_product f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ,
    quantumElectronMeasure_clusterProductSchwartz f h hfc hhc hnf hnh]

/-- The actual binary shuffle assembly preserves the ordered product's nuclear number measure. -/
theorem quantumNuclearMeasure_binaryClusterAssembly_eq_product :
    quantumNuclearMeasure ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumNuclearMeasure ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  apply Measure.ext_of_lintegral
  intro w hw
  rw [nuclear_measure_testing _ w hw, nuclear_measure_testing _ w hw]
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_weight_sum
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (nuclearWeight w) (nuclearWeight_measurable w hw)
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (∫⁻ X, nuclearWeight w X *
      (‖(clusterProductSchwartz f h hfc hhc).toLp 2 volume X‖₊ : ℝ≥0∞)^2)
    (fun p => by
      rw [← nuclear_measure_testing _ w hw, term_nuclearMeasure f h hfc hhc hfa hha hfs hhs p.1 p.2]
      exact nuclear_measure_testing _ w hw)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- Two normalized separated correlated inputs give the sum of their actual nuclear number measures. -/
theorem quantumNuclearMeasure_binaryClusterAssembly
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumNuclearMeasure ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumNuclearMeasure (f.toLp 2 volume) + quantumNuclearMeasure (h.toLp 2 volume) := by
  rw [quantumNuclearMeasure_binaryClusterAssembly_eq_product f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ,
    quantumNuclearMeasure_clusterProductSchwartz f h hfc hhc hnf hnh]

end LiebThirring

end
