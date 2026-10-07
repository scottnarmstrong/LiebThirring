/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterBasic
public import LiebThirring.ThermoClusters.ClusterTensor

/-! # Product integration for spatial-spin orbitals -/

public section
open MeasureTheory WithLp
open scoped ComplexConjugate
namespace LiebThirring

/-- The canonical identification of a one-particle configuration with its position. -/
@[expose] noncomputable def oneParticleConfigurationEquiv : Position ≃ₗᵢ[ℝ] Configuration 1 where
  toFun := oneParticleConfiguration
  invFun := fun x ↦ particlePosition x 0
  left_inv := fun x ↦ particlePosition_oneParticleConfiguration x 0
  right_inv := by
    intro x
    apply WithLp.ofLp_injective 2
    funext ia
    exact congrArg (fun i : Fin 1 ↦ x (i, ia.2)) (Subsingleton.elim 0 ia.1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_one]
    rfl

/-- The one-particle inner product written as a spatial integral and finite spin sum. -/
theorem orbital_inner_eq_integral {q : ℕ} (u v : State 1 q) :
    inner ℂ u v = ∫ x : Position, ∑ t : Fin q,
      starRingEnd ℂ (orbitalValue u x t) * orbitalValue v x t := by
  rw [MeasureTheory.L2.inner_def]
  have hmp : MeasurePreserving (oneParticleConfigurationEquiv : Position → Configuration 1)
      (volume : Measure Position) (volume : Measure (Configuration 1)) :=
    oneParticleConfigurationEquiv.measurePreserving
  calc
    _ = ∫ x : Position, inner ℂ (u (oneParticleConfigurationEquiv x))
        (v (oneParticleConfigurationEquiv x)) :=
      (hmp.integral_comp oneParticleConfigurationEquiv.toMeasurableEquiv.measurableEmbedding
        (fun x : Configuration 1 ↦ inner ℂ (u x) (v x))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply]
      let e : Fin q ≃ SpinLabels 1 q :=
        { toFun := oneParticleSpinLabel
          invFun := fun s ↦ s 0
          left_inv := fun _ ↦ rfl
          right_inv := fun s ↦ by funext i; exact congrArg s (Subsingleton.elim 0 i) }
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro t _
      simp only [RCLike.inner_apply]
      change orbitalValue v x t * starRingEnd ℂ (orbitalValue u x t) = _
      exact mul_comm _ _

/-- The pointwise spin contraction of two one-particle orbitals. -/
@[expose] noncomputable def orbitalContraction {q : ℕ} (u v : State 1 q) (x : Position) : ℂ :=
  ∑ t : Fin q, starRingEnd ℂ (orbitalValue u x t) * orbitalValue v x t

theorem integral_orbitalContraction {q : ℕ} (u v : State 1 q) :
    ∫ x : Position, orbitalContraction u v x = inner ℂ u v := by
  exact (orbital_inner_eq_integral u v).symm

theorem integrable_orbitalContraction {q : ℕ} (u v : State 1 q) :
    Integrable (orbitalContraction u v) := by
  have hmp : MeasurePreserving (oneParticleConfigurationEquiv : Position → Configuration 1)
      (volume : Measure Position) (volume : Measure (Configuration 1)) :=
    oneParticleConfigurationEquiv.measurePreserving
  have h := (hmp.integrable_comp_emb
    oneParticleConfigurationEquiv.toMeasurableEquiv.measurableEmbedding).mpr
      (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u v)
  refine h.congr ?_
  filter_upwards [] with x
  simp only [Function.comp_apply, oneParticleConfigurationEquiv, PiLp.inner_apply]
  let e : Fin q ≃ SpinLabels 1 q :=
    { toFun := oneParticleSpinLabel
      invFun := fun s ↦ s 0
      left_inv := fun _ ↦ rfl
      right_inv := fun s ↦ by funext i; exact congrArg s (Subsingleton.elim 0 i) }
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  simp only [RCLike.inner_apply]
  change orbitalValue v x t * starRingEnd ℂ (orbitalValue u x t) = _
  exact mul_comm _ _

/-- Split a configuration into two ordinary configuration factors. -/
@[expose] noncomputable def configurationClusterSplitPair (n k : ℕ) :
    Configuration (n + k) ≃ᵐ Configuration n × Configuration k :=
  (configurationClusterSplit n k).toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Configuration n × Configuration k)).symm

theorem measurePreserving_configurationClusterSplitPair (n k : ℕ) :
    MeasurePreserving (configurationClusterSplitPair n k) :=
  have h₁ : MeasurePreserving (configurationClusterSplit n k)
      (volume : Measure (Configuration (n+k)))
      (volume : Measure (WithLp 2 (Configuration n × Configuration k))) :=
    (configurationClusterSplit n k).measurePreserving
  have h₂ : MeasurePreserving (@WithLp.ofLp 2 (Configuration n × Configuration k))
      (volume : Measure (WithLp 2 (Configuration n × Configuration k)))
      (volume : Measure (Configuration n × Configuration k)) :=
    WithLp.volume_preserving_ofLp (Configuration n) (Configuration k)
  h₁.trans h₂

/-- Independent spatial-spin orbital contractions factor over all particles. -/
theorem integral_prod_orbitalContraction {N q : ℕ}
    (u v : Fin N → State 1 q) :
    (∫ x : Configuration N,
      ∏ i : Fin N, orbitalContraction (u i) (v i) (particlePosition x i)) =
      ∏ i : Fin N, inner ℂ (u i) (v i) := by
  induction N with
  | zero => simp [volume_euclideanSpace_eq_dirac]
  | succ N ih =>
      let e := configurationClusterSplitPair N 1
      have hmp : MeasurePreserving e := measurePreserving_configurationClusterSplitPair N 1
      calc
        _ = (∫ z : Configuration N × Configuration 1,
          (∏ i : Fin N, orbitalContraction (u i.castSucc) (v i.castSucc)
            (particlePosition z.1 i)) *
          orbitalContraction (u (Fin.last N)) (v (Fin.last N))
            (particlePosition z.2 0)) := by
            rw [← hmp.integral_comp']
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Fin.prod_univ_castSucc]
            rfl
        _ = _ := by
          rw [Measure.volume_eq_prod]
          rw [integral_prod_mul
            (fun x : Configuration N ↦
              ∏ i : Fin N, orbitalContraction (u i.castSucc) (v i.castSucc)
                (particlePosition x i))
            (fun x : Configuration 1 ↦
              orbitalContraction (u (Fin.last N)) (v (Fin.last N))
                (particlePosition x 0)),
            ih (fun i ↦ u i.castSucc) (fun i ↦ v i.castSucc)]
          have h₁ : MeasurePreserving
              (oneParticleConfigurationEquiv : Position → Configuration 1)
              (volume : Measure Position) (volume : Measure (Configuration 1)) :=
            oneParticleConfigurationEquiv.measurePreserving
          rw [← h₁.integral_comp
            oneParticleConfigurationEquiv.toMeasurableEquiv.measurableEmbedding]
          have heval (x : Position) : oneParticleConfigurationEquiv x =
              oneParticleConfiguration x := rfl
          simp only [heval, particlePosition_oneParticleConfiguration]
          rw [integral_orbitalContraction]
          rw [Fin.prod_univ_castSucc]

theorem integrable_prod_orbitalContraction {N q : ℕ}
    (u v : Fin N → State 1 q) :
    Integrable (fun x : Configuration N ↦
      ∏ i : Fin N, orbitalContraction (u i) (v i) (particlePosition x i)) := by
  induction N with
  | zero => simp [volume_euclideanSpace_eq_dirac]
  | succ N ih =>
      let e := configurationClusterSplitPair N 1
      have hmp : MeasurePreserving e := measurePreserving_configurationClusterSplitPair N 1
      have h₁ : MeasurePreserving
          (oneParticleConfigurationEquiv : Position → Configuration 1)
          (volume : Measure Position) (volume : Measure (Configuration 1)) :=
        oneParticleConfigurationEquiv.measurePreserving
      have hg : Integrable (fun x : Configuration 1 ↦
          orbitalContraction (u (Fin.last N)) (v (Fin.last N))
            (particlePosition x 0)) :=
        (h₁.integrable_comp_emb
          oneParticleConfigurationEquiv.toMeasurableEquiv.measurableEmbedding).mp <| by
            refine (integrable_orbitalContraction
              (u (Fin.last N)) (v (Fin.last N))).congr ?_
            filter_upwards [] with x
            have heval : oneParticleConfigurationEquiv x = oneParticleConfiguration x := rfl
            simp only [Function.comp_apply, heval, particlePosition_oneParticleConfiguration]
      have hp := Integrable.mul_prod
        (ih (fun i ↦ u i.castSucc) (fun i ↦ v i.castSucc))
        hg
      rw [← Measure.volume_eq_prod] at hp
      have hc := (hmp.integrable_comp_emb e.measurableEmbedding).mpr hp
      refine hc.congr ?_
      filter_upwards [] with x
      rw [Fin.prod_univ_castSucc]
      rfl

/-- Summing independent spin labels turns a product into the product of spin contractions. -/
theorem sum_prod_orbital_eq_prod_contraction {N q : ℕ}
    (u v : Fin N → State 1 q) (x : Configuration N) :
    (∑ s : SpinLabels N q, ∏ i : Fin N,
      starRingEnd ℂ (orbitalValue (u i) (particlePosition x i) (s i)) *
        orbitalValue (v i) (particlePosition x i) (s i)) =
      ∏ i : Fin N, orbitalContraction (u i) (v i) (particlePosition x i) := by
  classical
  simpa [Fintype.piFinset_univ, orbitalContraction] using
    (Finset.sum_prod_piFinset (R := ℂ) (Finset.univ : Finset (Fin q))
      (fun i t ↦ starRingEnd ℂ (orbitalValue (u i) (particlePosition x i) t) *
        orbitalValue (v i) (particlePosition x i) t))

end LiebThirring
end
