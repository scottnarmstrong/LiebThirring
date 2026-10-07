/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ShuffleSupport
public import LiebThirring.ThermoClusters.TensorKinetic
public import LiebThirring.ThermoClusters.TensorCoulomb
import LiebThirring.ThermoClusters.DisjointSum
import LiebThirring.ThermoForm.Algebra
import LiebThirring.Variational.TrialScaling
import LiebThirring.Assembly.IntegratedBaxter

/-! # Exact energies of the binary cluster assembly

The genuine double-quotient shuffle construction preserves both Fourier
kinetic energies and both positive Coulomb expectations of the ordered
product. Permutation and electronic signs preserve each summand's energy;
source confinement in disjoint regions supplies the actual disjoint closed
supports. The reciprocal square-root cardinal factor then cancels the
number of summands, including vacuum sectors.

For normalized correlated inputs the kinetic energies add, and repulsion
and attraction split into internal energies and the four one-body marginal
interactions. A separate finite-total-expectation corollary gives the real
Coulomb difference. Proof: cluster assembly.
-/

public section

open MeasureTheory Set Function WithLp
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring
private theorem normalize_card_coeff (k : ℕ) (hk : 0 < k) :
    (‖(Real.sqrt k)⁻¹‖₊ : ℝ≥0∞)^2 * (k : ℝ≥0∞) = 1 := by
  have hr : ‖(Real.sqrt k)⁻¹‖^2 * (k : ℝ) = 1 := by
    rw [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk.ne')
  have he := congrArg ENNReal.ofReal hr
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm, ENNReal.ofReal_natCast, ENNReal.ofReal_one] using he
private theorem normalize_card_energy (k : ℕ) (hk : 0 < k) (a : ℝ≥0∞) :
    (‖(Real.sqrt k)⁻¹‖₊ : ℝ≥0∞)^2 * ((k : ℝ≥0∞)*a) = a := by
  rw [← mul_assoc, normalize_card_coeff k hk, one_mul]
private theorem quantumSchwartz_toLp_real_smul {N M q : ℕ} (c : ℝ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (c • f).toLp 2 volume = (c : ℂ) • f.toLp 2 volume := by
  change SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2 volume (c • f) = _
  rw [map_smul]
  exact RCLike.real_smul_eq_coe_smul c _
private theorem quantumRepulsionEnergy_smul {N M q : ℕ} (z : ℕ) (c : ℂ)
    (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z (c • ψ) = (‖c‖₊ : ℝ≥0∞)^2 * quantumRepulsionEnergy z ψ := by
  unfold quantumRepulsionEnergy
  exact trial_lintegral_weight_smul _ c _
private theorem quantumAttractionEnergy_smul {N M q : ℕ} (z : ℕ) (c : ℂ)
    (ψ : QuantumState N M q) :
    quantumAttractionEnergy z (c • ψ) = (‖c‖₊ : ℝ≥0∞)^2 * quantumAttractionEnergy z ψ := by
  unfold quantumAttractionEnergy
  exact trial_lintegral_weight_smul _ c _
private theorem sign_norm_one {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    ‖((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))‖₊ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
private theorem quantumSchwartz_toLp_complex_smul {N M q : ℕ} (c : ℂ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume := by
  exact (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume).map_smul c f

private theorem electronEnergy_signedPermutation {N M q : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (η : Equiv.Perm α) (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumElectronKineticEnergy ((((((Equiv.Perm.sign η : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f).toLp 2 volume)) =
    quantumElectronKineticEnergy (f.toLp 2 volume) := by
  rw [quantumSchwartz_toLp_complex_smul, quantumElectronKineticEnergy_smul,
    sign_norm_one, ENNReal.coe_one, one_pow, one_mul, quantumSchwartzPermutation_toLp,
    quantumElectronKineticEnergy_quantumStatePermutation]
private theorem nuclearEnergy_signedPermutation {N M q : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (η : Equiv.Perm α) (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumNuclearKineticEnergy ((((((Equiv.Perm.sign η : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f).toLp 2 volume)) =
    quantumNuclearKineticEnergy (f.toLp 2 volume) := by
  rw [quantumSchwartz_toLp_complex_smul, quantumNuclearKineticEnergy_smul,
    sign_norm_one, ENNReal.coe_one, one_pow, one_mul, quantumSchwartzPermutation_toLp,
    quantumNuclearKineticEnergy_quantumStatePermutation]
private theorem repEnergy_signedPermutation {N M q : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (η : Equiv.Perm α) (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumRepulsionEnergy z ((((((Equiv.Perm.sign η : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f).toLp 2 volume)) =
    quantumRepulsionEnergy z (f.toLp 2 volume) := by
  rw [quantumSchwartz_toLp_complex_smul, quantumRepulsionEnergy_smul,
    sign_norm_one, ENNReal.coe_one, one_pow, one_mul, quantumSchwartzPermutation_toLp,
    quantumRepulsionEnergy_quantumStatePermutation]
private theorem attrEnergy_signedPermutation {N M q : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (η : Equiv.Perm α) (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumAttractionEnergy z ((((((Equiv.Perm.sign η : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f).toLp 2 volume)) =
    quantumAttractionEnergy z (f.toLp 2 volume) := by
  rw [quantumSchwartz_toLp_complex_smul, quantumAttractionEnergy_smul,
    sign_norm_one, ENNReal.coe_one, one_pow, one_mul, quantumSchwartzPermutation_toLp,
    quantumAttractionEnergy_quantumStatePermutation]

private theorem schwartz_weight_toLp {N M q : ℕ}
    (w : QuantumConfiguration N M → ℝ≥0∞)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (∫⁻ X, w X * (‖f.toLp 2 volume X‖₊ : ℝ≥0∞)^2) =
      ∫⁻ X, w X * (‖f X‖₊ : ℝ≥0∞)^2 := by
  apply lintegral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with X hX
  rw [hX]
private theorem measurable_repPotential (N M z : ℕ) :
    Measurable (fun X : QuantumConfiguration N M =>
      electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (particlePosition X.snd)) := by
  simp_rw [nuclearRepulsion_const_eq]
  exact (Assembly.measurable_electronRepulsion.comp (WithLp.fstL 2 ℝ _ _).continuous.measurable).add
    (measurable_const.mul (Assembly.measurable_electronRepulsion.comp
      (WithLp.sndL 2 ℝ _ _).continuous.measurable))
private theorem measurable_attrPotential (N M z : ℕ) :
    Measurable (fun X : QuantumConfiguration N M =>
      attraction (fun _ : Fin M => (z : ℝ≥0)) (particlePosition X.snd) X.fst) := by
  classical
  unfold attraction
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  have he : Measurable (fun X : QuantumConfiguration N M => particlePosition X.fst i) :=
    (measurable_particlePosition i).comp (WithLp.fstL 2 ℝ _ _).continuous.measurable
  have hn : Measurable (fun X : QuantumConfiguration N M => particlePosition X.snd k) :=
    (measurable_particlePosition k).comp (WithLp.sndL 2 ℝ _ _).continuous.measurable
  unfold coulombKernel
  exact measurable_const.mul (((he.sub hn).norm.ennreal_ofReal).inv)
private theorem repEnergy_disjoint_sum {ι : Type*} [Fintype ι] {N M q : ℕ} (z : ℕ)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    quantumRepulsionEnergy z ((∑ i, f i).toLp 2 volume) =
      ∑ i, quantumRepulsionEnergy z ((f i).toLp 2 volume) := by
  classical
  unfold quantumRepulsionEnergy
  simp only [schwartz_weight_toLp]
  exact quantumSchwartz_lintegral_weight_sum _ (measurable_repPotential N M z) f hf
private theorem attrEnergy_disjoint_sum {ι : Type*} [Fintype ι] {N M q : ℕ} (z : ℕ)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    quantumAttractionEnergy z ((∑ i, f i).toLp 2 volume) =
      ∑ i, quantumAttractionEnergy z ((f i).toLp 2 volume) := by
  classical
  unfold quantumAttractionEnergy
  simp only [schwartz_weight_toLp]
  exact quantumSchwartz_lintegral_weight_sum _ (measurable_attrPotential N M z) f hf

private theorem normalized_sum_electronkinetic {ι : Type*} [Fintype ι] {N M q : ℕ}
    (hι : 0 < Fintype.card ι)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (a : ℝ≥0∞) (he : ∀ i, quantumElectronKineticEnergy ((f i).toLp 2 volume) = a) :
    quantumElectronKineticEnergy (((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2 volume) = a := by
  classical
  rw [quantumSchwartz_toLp_real_smul, quantumElectronKineticEnergy_smul, quantumElectronKineticEnergy_disjoint_schwartz_sum f hf]
  simp only [Complex.nnnorm_real, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact normalize_card_energy _ hι a

private theorem normalized_sum_nuclearkinetic {ι : Type*} [Fintype ι] {N M q : ℕ}
    (hι : 0 < Fintype.card ι)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (a : ℝ≥0∞) (he : ∀ i, quantumNuclearKineticEnergy ((f i).toLp 2 volume) = a) :
    quantumNuclearKineticEnergy (((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2 volume) = a := by
  classical
  rw [quantumSchwartz_toLp_real_smul, quantumNuclearKineticEnergy_smul, quantumNuclearKineticEnergy_disjoint_schwartz_sum f hf]
  simp only [Complex.nnnorm_real, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact normalize_card_energy _ hι a

private theorem normalized_sum_repulsion {ι : Type*} [Fintype ι] {N M q : ℕ} (z : ℕ)
    (hι : 0 < Fintype.card ι)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (a : ℝ≥0∞) (he : ∀ i, quantumRepulsionEnergy z ((f i).toLp 2 volume) = a) :
    quantumRepulsionEnergy z (((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2 volume) = a := by
  classical
  rw [quantumSchwartz_toLp_real_smul, quantumRepulsionEnergy_smul, repEnergy_disjoint_sum z f hf]
  simp only [Complex.nnnorm_real, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact normalize_card_energy _ hι a

private theorem normalized_sum_attraction {ι : Type*} [Fintype ι] {N M q : ℕ} (z : ℕ)
    (hι : 0 < Fintype.card ι)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (a : ℝ≥0∞) (he : ∀ i, quantumAttractionEnergy z ((f i).toLp 2 volume) = a) :
    quantumAttractionEnergy z (((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2 volume) = a := by
  classical
  rw [quantumSchwartz_toLp_real_smul, quantumAttractionEnergy_smul, attrEnergy_disjoint_sum z f hf]
  simp only [Complex.nnnorm_real, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact normalize_card_energy _ hι a

variable {n₁ n₂ m₁ m₂ q : ℕ}
variable (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
  (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
  (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
  (hfa : quantum_antisymmetric (f.toLp 2 volume))
  (hha : quantum_antisymmetric (h.toLp 2 volume))
  (hfs : nuclear_symmetric (f.toLp 2 volume))
  (hhs : nuclear_symmetric (h.toLp 2 volume))

private theorem term_electronkinetic
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumElectronKineticEnergy ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumElectronKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk]
  exact electronEnergy_signedPermutation σ (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
    (clusterProductSchwartz f h hfc hhc)

private theorem term_nuclearkinetic
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumNuclearKineticEnergy ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumNuclearKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk]
  exact nuclearEnergy_signedPermutation σ (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
    (clusterProductSchwartz f h hfc hhc)

private theorem term_repulsion (z : ℕ)
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumRepulsionEnergy z ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumRepulsionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk]
  exact repEnergy_signedPermutation σ (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ) z
    (clusterProductSchwartz f h hfc hhc)

private theorem term_attraction (z : ℕ)
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumAttractionEnergy z ((binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume) =
      quantumAttractionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  rw [binaryClusterShuffleTerm_mk_mk]
  exact attrEnergy_signedPermutation σ (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ) z
    (clusterProductSchwartz f h hfc hhc)

variable (Ω₁ Ω₂ : Set Position)
  (hfp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₁)})
  (hhp : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₂)})
  (hΩ : Disjoint Ω₁ Ω₂)

include hfp hhp hΩ

/-- The actual binary shuffle assembly preserves the ordered product's electronkinetic energy. -/
theorem quantumElectronKineticEnergy_binaryClusterAssembly :
    quantumElectronKineticEnergy ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumElectronKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_sum_electronkinetic
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (quantumElectronKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume))
    (fun p => term_electronkinetic f h hfc hhc hfa hha hfs hhs p.1 p.2)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- The actual binary shuffle assembly preserves the ordered product's nuclearkinetic energy. -/
theorem quantumNuclearKineticEnergy_binaryClusterAssembly :
    quantumNuclearKineticEnergy ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumNuclearKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_sum_nuclearkinetic
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (quantumNuclearKineticEnergy ((clusterProductSchwartz f h hfc hhc).toLp 2 volume))
    (fun p => term_nuclearkinetic f h hfc hhc hfa hha hfs hhs p.1 p.2)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- The actual binary shuffle assembly preserves the ordered product's repulsion energy. -/
theorem quantumRepulsionEnergy_binaryClusterAssembly (z : ℕ) :
    quantumRepulsionEnergy z ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumRepulsionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_sum_repulsion z
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (quantumRepulsionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume))
    (fun p => term_repulsion f h hfc hhc hfa hha hfs hhs z p.1 p.2)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- The actual binary shuffle assembly preserves the ordered product's attraction energy. -/
theorem quantumAttractionEnergy_binaryClusterAssembly (z : ℕ) :
    quantumAttractionEnergy z ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumAttractionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume) := by
  classical
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have he := normalized_sum_attraction z
    (ι := Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) Fintype.card_pos
    (fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2) hd
    (quantumAttractionEnergy z ((clusterProductSchwartz f h hfc hhc).toLp 2 volume))
    (fun p => term_attraction f h hfc hhc hfa hha hfs hhs z p.1 p.2)
  simpa only [binaryClusterAssembly, binaryClusterShuffleSum, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_mul] using he

/-- Normalized separated correlated inputs give additive electron kinetic energy after assembly. -/
theorem quantumElectronKineticEnergy_binaryClusterAssembly_of_normalized
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumElectronKineticEnergy ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumElectronKineticEnergy (f.toLp 2 volume) + quantumElectronKineticEnergy (h.toLp 2 volume) := by
  rw [quantumElectronKineticEnergy_binaryClusterAssembly f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ,
    quantumElectronKineticEnergy_clusterProductSchwartz_of_normalized f h hfc hhc hnf hnh]

/-- Normalized separated correlated inputs give additive nuclear kinetic energy after assembly. -/
theorem quantumNuclearKineticEnergy_binaryClusterAssembly_of_normalized
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumNuclearKineticEnergy ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) =
      quantumNuclearKineticEnergy (f.toLp 2 volume) + quantumNuclearKineticEnergy (h.toLp 2 volume) := by
  rw [quantumNuclearKineticEnergy_binaryClusterAssembly f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ,
    quantumNuclearKineticEnergy_clusterProductSchwartz_of_normalized f h hfc hhc hnf hnh]

/-- The real Coulomb difference of the actual binary assembly, with finite total expectations. -/
theorem binaryClusterAssembly_coulomb_toReal_of_finite (z : ℕ)
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1)
    (hR : quantumRepulsionEnergy z ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) < ⊤)
    (hA : quantumAttractionEnergy z ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) < ⊤) :
    let ψ := f.toLp 2 volume
    let χ := h.toLp 2 volume
    let Ψ := (binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume
    (quantumRepulsionEnergy z Ψ).toReal - (quantumAttractionEnergy z Ψ).toReal =
      ((quantumRepulsionEnergy z ψ).toReal - (quantumAttractionEnergy z ψ).toReal) +
      ((quantumRepulsionEnergy z χ).toReal - (quantumAttractionEnergy z χ).toReal) +
      (clusterCoulombInteraction (quantumElectronMeasure ψ) (quantumElectronMeasure χ)).toReal +
      (z : ℝ)^2 * (clusterCoulombInteraction (quantumNuclearMeasure ψ) (quantumNuclearMeasure χ)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumElectronMeasure ψ) (quantumNuclearMeasure χ)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumNuclearMeasure ψ) (quantumElectronMeasure χ)).toReal := by
  dsimp only
  have hr := quantumRepulsionEnergy_binaryClusterAssembly f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ z
  have ha := quantumAttractionEnergy_binaryClusterAssembly f h hfc hhc hfa hha hfs hhs Ω₁ Ω₂ hfp hhp hΩ z
  rw [hr] at hR
  rw [ha] at hA
  rw [hr, ha]
  exact clusterProductSchwartz_coulomb_toReal_of_finite z f h hfc hhc hnf hnh hR hA

end LiebThirring

end
