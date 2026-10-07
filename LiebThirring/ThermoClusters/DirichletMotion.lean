/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Domains
public import LiebThirring.ThermoClusters.CoulombMotion
public import LiebThirring.ThermoClusters.KineticMotion
public import LiebThirring.ThermoForm.NormalizedCore

/-!
# Rigid transport of Dirichlet regions

Compact Schwartz approximants are transported by inverse simultaneous rigid
motion, preserving the exact joint kinetic graph closure and both statistics.
The resulting form-domain bijection preserves the energy and its
variational infimum for every spatial region.

-/

public section
open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- Inverse rigid pullback of a Schwartz joint trial. -/
@[expose] noncomputable def quantumSchwartzMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    𝓢(QuantumConfiguration N M, SpinAmplitudes N q) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (quantumRotation Q).symm.toContinuousLinearEquiv f).compSubConstCLM ℂ (quantumShift N M c)

/-- Forward rigid pullback, inverse to the Schwartz state action. -/
@[expose] noncomputable def quantumSchwartzMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    𝓢(QuantumConfiguration N M, SpinAmplitudes N q) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (quantumRotation Q).toContinuousLinearEquiv (f.compSubConstCLM ℂ (-quantumShift N M c))

@[simp] theorem quantumSchwartzMotionInverse_apply {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (X : QuantumConfiguration N M) :
    quantumSchwartzMotionInverse Q c f X = f (quantumRigidMotion Q c X) := by
  change f (quantumRotation Q X - -quantumShift N M c) = _
  rw [sub_neg_eq_add]
  rfl

/-- The transformed Schwartz trial represents the transported L² state exactly. -/
theorem quantumSchwartzMotion_toLp {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (quantumSchwartzMotion Q c f).toLp 2 volume = quantumStateMotion Q c (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(quantumSchwartzMotion Q c f).coeFn_toLp 2 volume,
    coeFn_quantumStateMotion Q c (f.toLp 2 volume),
    (measurePreserving_quantumRigidMotion_symm Q c).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 volume)] with X hX hmotion hf
  rw [hX, hmotion]
  exact hf.symm

theorem quantumSchwartzMotionInverse_toLp {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (quantumSchwartzMotionInverse Q c f).toLp 2 volume =
      quantumStateMotionInverse Q c (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(quantumSchwartzMotionInverse Q c f).coeFn_toLp 2 volume,
    coeFn_quantumStateMotionInverse Q c (f.toLp 2 volume),
    (measurePreserving_quantumRigidMotion Q c).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 volume)] with X hX hmotion hf
  rw [hX, hmotion, quantumSchwartzMotionInverse_apply]
  exact hf.symm

theorem tsupport_quantumSchwartzMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    tsupport (quantumSchwartzMotion Q c f) = quantumRigidMotion Q c '' tsupport f := by
  change tsupport ((fun X => f X) ∘ (quantumRigidMotion Q c).toHomeomorph.symm) = _
  rw [tsupport_comp_eq_preimage, Homeomorph.preimage_symm]
  rfl

theorem tsupport_quantumSchwartzMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    tsupport (quantumSchwartzMotionInverse Q c f) = quantumRigidMotion Q c ⁻¹' tsupport f := by
  have heq : (quantumSchwartzMotionInverse Q c f : QuantumConfiguration N M → SpinAmplitudes N q) =
      (f : QuantumConfiguration N M → SpinAmplitudes N q) ∘ (quantumRigidMotion Q c).toHomeomorph := by
    funext X
    exact quantumSchwartzMotionInverse_apply Q c f X
  rw [heq, tsupport_comp_eq_preimage]
  rfl

/-- Centered physical balls become balls about the translation centre. -/
theorem image_spatialRigidMotion_ball_zero (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (L : ℝ) :
    spatialRigidMotion Q c '' Metric.ball (0 : Position) L = Metric.ball c L := by
  change (spatialRigidMotion Q c).toIsometryEquiv '' Metric.ball (0 : Position) L = _
  rw [IsometryEquiv.image_ball]
  have hzero : spatialRigidMotion Q c 0 = c := by
    calc
      spatialRigidMotion Q c 0 = Q 0 + c := rfl
      _ = c := by rw [map_zero, zero_add]
  simp only [AffineIsometryEquiv.coe_toIsometryEquiv, hzero]

/-- Both kinetic graph errors are exactly preserved by rigid transport. -/
theorem quantumGraphError_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (ψ φ : QuantumState N M q) :
    quantumGraphError m (quantumStateMotion Q c ψ) (quantumStateMotion Q c φ) =
      quantumGraphError m ψ φ := by
  unfold quantumGraphError
  rw [← map_sub, norm_quantumStateMotion, quantumElectronKineticEnergy_quantumStateMotion,
    quantumNuclearKineticEnergy_quantumStateMotion]

theorem quantumGraphError_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (ψ φ : QuantumState N M q) :
    quantumGraphError m (quantumStateMotionInverse Q c ψ) (quantumStateMotionInverse Q c φ) =
      quantumGraphError m ψ φ := by
  have h := quantumGraphError_quantumStateMotion Q c m
    (quantumStateMotionInverse Q c ψ) (quantumStateMotionInverse Q c φ)
  simpa only [quantumStateMotion_quantumStateMotionInverse] using h.symm

/-- Every compact Schwartz approximant transports to the image spatial region. -/
theorem is_dirichlet_region_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (Ω : Set Position) (ψ : QuantumState N M q) (hψ : is_dirichlet_region m Ω ψ) :
    is_dirichlet_region m (spatialRigidMotion Q c '' Ω) (quantumStateMotion Q c ψ) := by
  intro ε hε
  obtain ⟨f, hc, hs, he, hn, hg⟩ := hψ ε hε
  refine ⟨quantumSchwartzMotion Q c f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tsupport_quantumSchwartzMotion]
    exact hc.image (quantumRigidMotion Q c).continuous
  · rw [tsupport_quantumSchwartzMotion]
    rintro X ⟨Y, hY, rfl⟩
    refine ⟨fun i => ?_, fun k => ?_⟩
    · exact ⟨particlePosition Y.fst i, (hs hY).1 i,
        (particlePosition_quantumRigidMotion_fst Q c Y i).symm⟩
    · exact ⟨particlePosition Y.snd k, (hs hY).2 k,
        (particlePosition_quantumRigidMotion_snd Q c Y k).symm⟩
  · rw [quantumSchwartzMotion_toLp]
    exact quantum_antisymmetric_quantumStateMotion Q c _ he
  · rw [quantumSchwartzMotion_toLp]
    exact nuclear_symmetric_quantumStateMotion Q c _ hn
  · change quantumGraphError m (quantumStateMotion Q c ψ)
      ((quantumSchwartzMotion Q c f).toLp 2 volume) < ENNReal.ofReal ε
    rw [quantumSchwartzMotion_toLp, quantumGraphError_quantumStateMotion]
    exact hg

/-- The inverse motion transports the image-region closure back to the original region. -/
theorem is_dirichlet_region_quantumStateMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (Ω : Set Position) (ψ : QuantumState N M q)
    (hψ : is_dirichlet_region m (spatialRigidMotion Q c '' Ω) ψ) :
    is_dirichlet_region m Ω (quantumStateMotionInverse Q c ψ) := by
  intro ε hε
  obtain ⟨f, hc, hs, he, hn, hg⟩ := hψ ε hε
  refine ⟨quantumSchwartzMotionInverse Q c f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tsupport_quantumSchwartzMotionInverse]
    exact (quantumRigidMotion Q c).toHomeomorph.isCompact_preimage.mpr hc
  · rw [tsupport_quantumSchwartzMotionInverse]
    intro X hX
    refine ⟨fun i => ?_, fun k => ?_⟩
    · have hp := (hs hX).1 i
      rw [particlePosition_quantumRigidMotion_fst] at hp
      change spatialRigidMotion Q c (particlePosition X.fst i) ∈ spatialRigidMotion Q c '' Ω at hp
      obtain ⟨y, hy, hyeq⟩ := hp
      exact (spatialRigidMotion Q c).injective hyeq ▸ hy
    · have hp := (hs hX).2 k
      rw [particlePosition_quantumRigidMotion_snd] at hp
      change spatialRigidMotion Q c (particlePosition X.snd k) ∈ spatialRigidMotion Q c '' Ω at hp
      obtain ⟨y, hy, hyeq⟩ := hp
      exact (spatialRigidMotion Q c).injective hyeq ▸ hy
  · rw [quantumSchwartzMotionInverse_toLp]
    exact quantum_antisymmetric_quantumStateMotionInverse Q c _ he
  · rw [quantumSchwartzMotionInverse_toLp]
    exact nuclear_symmetric_quantumStateMotionInverse Q c _ hn
  · change quantumGraphError m (quantumStateMotionInverse Q c ψ)
      ((quantumSchwartzMotionInverse Q c f).toLp 2 volume) < ENNReal.ofReal ε
    rw [quantumSchwartzMotionInverse_toLp, quantumGraphError_quantumStateMotionInverse]
    exact hg

/-- Exact covariance of the graph closure generalized to an arbitrary spatial region. -/
theorem is_dirichlet_region_quantumStateMotion_iff {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (Ω : Set Position) (ψ : QuantumState N M q) :
    is_dirichlet_region m Ω ψ ↔
      is_dirichlet_region m (spatialRigidMotion Q c '' Ω) (quantumStateMotion Q c ψ) := by
  constructor
  · exact is_dirichlet_region_quantumStateMotion Q c m Ω ψ
  · intro hψ
    have h := is_dirichlet_region_quantumStateMotionInverse Q c m Ω _ hψ
    simpa only [quantumStateMotionInverse_quantumStateMotion] using h

/-- Rigid transport restricts to the exact finite-kinetic form domain. -/
@[expose] noncomputable def quantumFormDomainMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumFormDomain N M q) :
    QuantumFormDomain N M q :=
  ⟨quantumStateMotion Q c ψ.val,
    quantum_antisymmetric_quantumStateMotion Q c ψ.val ψ.property.1,
    nuclear_symmetric_quantumStateMotion Q c ψ.val ψ.property.2.1,
    by rw [quantumElectronKineticEnergy_quantumStateMotion]; exact ψ.property.2.2.1,
    by rw [quantumNuclearKineticEnergy_quantumStateMotion]; exact ψ.property.2.2.2⟩

/-- Forward-coordinate pullback restricts to the same exact form domain. -/
@[expose] noncomputable def quantumFormDomainMotionInverse {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumFormDomain N M q) :
    QuantumFormDomain N M q :=
  ⟨quantumStateMotionInverse Q c ψ.val,
    quantum_antisymmetric_quantumStateMotionInverse Q c ψ.val ψ.property.1,
    nuclear_symmetric_quantumStateMotionInverse Q c ψ.val ψ.property.2.1,
    by
      have h := quantumElectronKineticEnergy_quantumStateMotion Q c (quantumStateMotionInverse Q c ψ.val)
      rw [quantumStateMotion_quantumStateMotionInverse] at h
      rw [← h]
      exact ψ.property.2.2.1,
    by
      have h := quantumNuclearKineticEnergy_quantumStateMotion Q c (quantumStateMotionInverse Q c ψ.val)
      rw [quantumStateMotion_quantumStateMotionInverse] at h
      rw [← h]
      exact ψ.property.2.2.2⟩

/-- The finite-kinetic form domain is preserved bijectively. -/
@[expose] noncomputable def quantumFormDomainMotionEquiv {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    QuantumFormDomain N M q ≃ QuantumFormDomain N M q where
  toFun := quantumFormDomainMotion Q c
  invFun := quantumFormDomainMotionInverse Q c
  left_inv ψ := Subtype.ext (quantumStateMotionInverse_quantumStateMotion Q c ψ.val)
  right_inv ψ := Subtype.ext (quantumStateMotion_quantumStateMotionInverse Q c ψ.val)

/-- The complete real quadratic energy is unchanged by form-domain transport. -/
@[simp] theorem quantumEnergy_quantumFormDomainMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q) :
    quantumEnergy z m (quantumFormDomainMotion Q c ψ) = quantumEnergy z m ψ := by
  simp only [quantumEnergy, quantumCoulombEnergy, quantumFormDomainMotion,
    quantumElectronKineticEnergy_quantumStateMotion, quantumNuclearKineticEnergy_quantumStateMotion,
    quantumRepulsionEnergy_quantumStateMotion, quantumAttractionEnergy_quantumStateMotion]

/-- The exact region form domains are in bijection under the simultaneous motion. -/
@[expose] noncomputable def dirichletRegionFormDomainMotionEquiv {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) :
    DirichletRegionFormDomain N M q m Ω ≃
      DirichletRegionFormDomain N M q m (spatialRigidMotion Q c '' Ω) :=
  Equiv.subtypeEquiv (quantumFormDomainMotionEquiv Q c)
    (fun ψ => is_dirichlet_region_quantumStateMotion_iff Q c m Ω ψ.val)

/-- The variational energy on every spatial region is rigid-motion invariant. -/
theorem dirichletRegionGroundStateEnergy_image_spatialRigidMotion (N M q z : ℕ)
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) :
    dirichletRegionGroundStateEnergy N M q z m (spatialRigidMotion Q c '' Ω) =
      dirichletRegionGroundStateEnergy N M q z m Ω := by
  let e := dirichletRegionFormDomainMotionEquiv (N := N) (M := M) (q := q) Q c m Ω
  let e₁ : {ψ : DirichletRegionFormDomain N M q m Ω // ‖ψ.val.val‖ = 1} ≃
      {ψ : DirichletRegionFormDomain N M q m (spatialRigidMotion Q c '' Ω) // ‖ψ.val.val‖ = 1} :=
    Equiv.subtypeEquiv e (fun ψ => by
      change ‖ψ.val.val‖ = 1 ↔ ‖quantumStateMotion Q c ψ.val.val‖ = 1
      rw [norm_quantumStateMotion])
  unfold dirichletRegionGroundStateEnergy
  apply (Equiv.iInf_congr e₁ (fun ψ => ?_)).symm
  change (quantumEnergy z m (quantumFormDomainMotion Q c ψ.val.val) : EReal) =
    (quantumEnergy z m ψ.val.val : EReal)
  rw [quantumEnergy_quantumFormDomainMotion]

/-- Confined centered balls and their translated balls have the same variational energy. -/
theorem dirichletRegionGroundStateEnergy_ball_center (N M q z : ℕ)
    (c : Position) (m : {m : ℝ≥0 // 0 < m})
    (L : {L : ℝ // 0 < L}) :
    dirichletRegionGroundStateEnergy N M q z m (Metric.ball c L.val) =
      confinedGroundStateEnergy N M q z m L := by
  rw [← image_spatialRigidMotion_ball_zero (LinearIsometryEquiv.refl ℝ Position) c L.val,
    dirichletRegionGroundStateEnergy_image_spatialRigidMotion,
    dirichletRegionGroundStateEnergy_ball]

end LiebThirring
end
