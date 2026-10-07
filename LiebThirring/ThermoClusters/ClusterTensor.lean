/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Rigid
public import LiebThirring.Thermodynamic.QuantumState
import LiebThirring.Kinetic.CurryingProductBasic

/-! # Ordered products of correlated joint cluster states

Spatial coordinates are regrouped by genuine volume-preserving linear
isometries. Spin amplitudes are tensored by the explicit label equivalence.
The resulting compact smooth joint wavefunction has exactly factoring mass
and product-weight expectations, including all vacuum sectors.
Lieb–Lebowitz (1972) II.E before (2.25).
-/

public section
open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap
namespace LiebThirring

@[expose] noncomputable def configurationClusterSplit (n k : ℕ) :
    Configuration (n+k) ≃ₗᵢ[ℝ] WithLp 2 (Configuration n × Configuration k) :=
  (configurationPositionEquiv (n+k)).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ Position finSumFinEquiv.symm).trans
      ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin k => Position)).trans
        (LinearIsometryEquiv.withLpProdCongr 2 (configurationPositionEquiv n).symm
          (configurationPositionEquiv k).symm)))

@[expose] noncomputable def jointBlockInterchange (A B C D : Type*)
    [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C] [NormedAddCommGroup D]
    [NormedSpace ℝ A] [NormedSpace ℝ B] [NormedSpace ℝ C] [NormedSpace ℝ D] :
    WithLp 2 (WithLp 2 (A × B) × WithLp 2 (C × D)) ≃ₗᵢ[ℝ]
      WithLp 2 (WithLp 2 (A × C) × WithLp 2 (B × D)) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ _).trans
    ((LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ _) (WithLp.linearEquiv 2 ℝ _)).trans
      ((LinearEquiv.prodProdProdComm ℝ A B C D).trans
        ((LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ _).symm
          (WithLp.linearEquiv 2 ℝ _).symm).trans (WithLp.linearEquiv 2 ℝ _).symm)))
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2]
    change (‖x.fst.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2) +
      (‖x.fst.snd‖ ^ 2 + ‖x.snd.snd‖ ^ 2) =
      (‖x.fst.fst‖ ^ 2 + ‖x.fst.snd‖ ^ 2) +
      (‖x.snd.fst‖ ^ 2 + ‖x.snd.snd‖ ^ 2)
    ring

@[expose] noncomputable def quantumClusterSplit (n₁ n₂ m₁ m₂ : ℕ) :
    QuantumConfiguration (n₁+n₂) (m₁+m₂) ≃ₗᵢ[ℝ]
      WithLp 2 (QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂) :=
  (LinearIsometryEquiv.withLpProdCongr 2 (configurationClusterSplit n₁ n₂)
    (configurationClusterSplit m₁ m₂)).trans (jointBlockInterchange _ _ _ _)

@[expose] noncomputable def clusterSpinEquiv (n₁ n₂ q : ℕ) :
    SpinLabels n₁ q × SpinLabels n₂ q ≃ SpinLabels (n₁+n₂) q :=
  (Equiv.sumArrowEquivProdArrow (Fin n₁) (Fin n₂) (Fin q)).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))

@[expose] noncomputable def clusterSpinTensor {n₁ n₂ q : ℕ}
    (u : SpinAmplitudes n₁ q) (v : SpinAmplitudes n₂ q) : SpinAmplitudes (n₁+n₂) q :=
  toLp 2 (fun s => u ((clusterSpinEquiv n₁ n₂ q).symm s).1 *
    v ((clusterSpinEquiv n₁ n₂ q).symm s).2)

theorem norm_clusterSpinTensor_sq {n₁ n₂ q : ℕ}
    (u : SpinAmplitudes n₁ q) (v : SpinAmplitudes n₂ q) :
    ‖clusterSpinTensor u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, ← (clusterSpinEquiv n₁ n₂ q).sum_comp]
  simp only [clusterSpinTensor, PiLp.toLp_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]

@[expose] noncomputable def clusterProduct {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) : SpinAmplitudes (n₁+n₂) q :=
  clusterSpinTensor (f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst)
    (h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd)

theorem clusterProduct_norm_sq {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    ‖clusterProduct f h X‖ ^ 2 =
      ‖f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst‖ ^ 2 *
      ‖h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd‖ ^ 2 :=
  norm_clusterSpinTensor_sq _ _

theorem clusterProduct_nnnorm_sq {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    (‖clusterProduct f h X‖₊ : ℝ≥0∞) ^ 2 =
      (‖f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst‖₊ : ℝ≥0∞) ^ 2 *
      (‖h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd‖₊ : ℝ≥0∞) ^ 2 := by
  have he := congrArg ENNReal.ofReal (clusterProduct_norm_sq f h X)
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm] using he

theorem contDiff_clusterProduct {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (clusterProduct f h) := by
  apply (contDiff_piLp 2).mpr
  intro s
  exact (((contDiff_piLp 2).mp hf _).comp
    ((WithLp.fstL 2 ℝ _ _).contDiff.comp
      (quantumClusterSplit n₁ n₂ m₁ m₂).toContinuousLinearEquiv.contDiff)).mul
    (((contDiff_piLp 2).mp hh _).comp
      ((WithLp.sndL 2 ℝ _ _).contDiff.comp
        (quantumClusterSplit n₁ n₂ m₁ m₂).toContinuousLinearEquiv.contDiff))

@[expose] noncomputable def quantumClusterSplitHomeomorph (n₁ n₂ m₁ m₂ : ℕ) :
    QuantumConfiguration (n₁+n₂) (m₁+m₂) ≃ₜ
      QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ :=
  (quantumClusterSplit n₁ n₂ m₁ m₂).toHomeomorph.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toHomeomorph

theorem measurePreserving_quantumClusterSplit (n₁ n₂ m₁ m₂ : ℕ) :
    MeasurePreserving (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂)
      volume (volume.prod volume) := by
  exact (WithLp.volume_preserving_ofLp _ _).comp
    (quantumClusterSplit n₁ n₂ m₁ m₂).measurePreserving

theorem hasCompactSupport_clusterProduct {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (hf : HasCompactSupport f) (hh : HasCompactSupport h) :
    HasCompactSupport (clusterProduct f h) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).isCompact_preimage.mpr (hf.prod hh))
  intro X hX
  refine ⟨subset_tsupport f ?_, subset_tsupport h ?_⟩
  · intro hz
    change f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst = 0 at hz
    apply hX
    ext s
    simp only [clusterProduct, clusterSpinTensor, hz, PiLp.zero_apply, PiLp.toLp_apply,
      zero_mul]
  · intro hz
    change h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd = 0 at hz
    apply hX
    ext s
    simp only [clusterProduct, clusterSpinTensor, hz, PiLp.zero_apply, PiLp.toLp_apply,
      mul_zero]

@[expose] noncomputable def clusterProductSchwartz {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X)) :
    𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂), SpinAmplitudes (n₁+n₂) q) :=
  (hasCompactSupport_clusterProduct (fun X => f X) (fun X => h X) hf hh).toSchwartzMap
    (contDiff_clusterProduct (fun X => f X) (fun X => h X) (f.smooth ⊤) (h.smooth ⊤))

theorem clusterProduct_lintegral_weight {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q) (hf : Measurable f)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q) (hh : Measurable h)
    (w₁ : QuantumConfiguration n₁ m₁ → ℝ≥0∞) (hw₁ : Measurable w₁)
    (w₂ : QuantumConfiguration n₂ m₂ → ℝ≥0∞) (hw₂ : Measurable w₂) :
    (∫⁻ X, w₁ (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst *
      w₂ (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd *
      (‖clusterProduct f h X‖₊ : ℝ≥0∞) ^ 2) =
    (∫⁻ X, w₁ X * (‖f X‖₊ : ℝ≥0∞) ^ 2) *
      (∫⁻ Y, w₂ Y * (‖h Y‖₊ : ℝ≥0∞) ^ 2) := by
  simp only [clusterProduct_nnnorm_sq]
  change (∫⁻ X, (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
    w₁ Z.1 * w₂ Z.2 * ((‖f Z.1‖₊ : ℝ≥0∞)^2 * (‖h Z.2‖₊ : ℝ≥0∞)^2))
      (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)) = _
  rw [(measurePreserving_quantumClusterSplit n₁ n₂ m₁ m₂).lintegral_comp_emb
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).toMeasurableEquiv.measurableEmbedding
      (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
        w₁ Z.1 * w₂ Z.2 * ((‖f Z.1‖₊ : ℝ≥0∞)^2 * (‖h Z.2‖₊ : ℝ≥0∞)^2))]
  have he (Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂) :
      w₁ Z.1 * w₂ Z.2 * ((‖f Z.1‖₊ : ℝ≥0∞)^2 * (‖h Z.2‖₊ : ℝ≥0∞)^2) =
      (w₁ Z.1 * (‖f Z.1‖₊ : ℝ≥0∞)^2) * (w₂ Z.2 * (‖h Z.2‖₊ : ℝ≥0∞)^2) := by
    ac_rfl
  simp only [he]
  exact lintegral_prod_mul (hw₁.mul (hf.nnnorm.coe_nnreal_ennreal.pow_const 2)).aemeasurable
    (hw₂.mul (hh.nnnorm.coe_nnreal_ennreal.pow_const 2)).aemeasurable

private theorem schwartz_joint_mass {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (∫⁻ X, (‖f X‖₊ : ℝ≥0∞)^2) = (‖f.toLp 2 volume‖₊ : ℝ≥0∞)^2 := by
  calc
    _ = ∫⁻ X, ‖(f.toLp 2 volume) X‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume] with X hX
      rw [hX, enorm_eq_nnnorm]
    _ = _ := by simpa only [enorm_eq_nnnorm] using lintegral_l2_enorm_sq (f.toLp 2 volume)

/-- The ordered tensor has the product of the two actual L² norms. -/
theorem norm_clusterProductSchwartz_toLp {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X)) :
    ‖(clusterProductSchwartz f h hf hh).toLp 2 volume‖ =
      ‖f.toLp 2 volume‖ * ‖h.toLp 2 volume‖ := by
  have he := clusterProduct_lintegral_weight (fun X => f X) f.continuous.measurable
    (fun X => h X) h.continuous.measurable (fun _ => 1) measurable_const
    (fun _ => 1) measurable_const
  simp only [one_mul] at he
  change (∫⁻ X, (‖clusterProductSchwartz f h hf hh X‖₊ : ℝ≥0∞)^2) = _ at he
  rw [schwartz_joint_mass, schwartz_joint_mass, schwartz_joint_mass] at he
  have hre := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    coe_nnnorm] at hre
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using hre

end LiebThirring
end
