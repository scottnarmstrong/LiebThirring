/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumConfiguration

/-!
# Simultaneous spatial rigid motions

A single orthogonal spatial map and translation act on every electron and nucleus.
The joint motion is an affine isometry preserving Lebesgue volume, including empty sectors.
change of all spatial coordinates.
-/

public section
open MeasureTheory WithLp
namespace LiebThirring

/-- The physical spatial motion, acting equally on both species. -/
@[expose] noncomputable def spatialRigidMotion (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    Position ≃ᵃⁱ[ℝ] Position :=
  Q.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ c)

/-- Regroup the three real coordinates of each particle into physical positions. -/
@[expose] noncomputable def configurationPositionEquiv (N : ℕ) :
    Configuration N ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin N => Position) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.sigmaEquivProd (Fin N) (Fin 3)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin N) (_ : Fin 3) => ℝ))

/-- Apply the same spatial orthogonal map to every particle. -/
@[expose] noncomputable def configurationRotation {N : ℕ} (Q : Position ≃ₗᵢ[ℝ] Position) :
    Configuration N ≃ₗᵢ[ℝ] Configuration N :=
  (configurationPositionEquiv N).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin N => Q)).trans
      (configurationPositionEquiv N).symm)

/-- The configuration translating every particle by the same vector. -/
@[expose] def configurationShift (N : ℕ) (c : Position) : Configuration N :=
  toLp 2 (fun ia => c ia.2)

/-- The joint orthogonal action on electron and nucleus positions. -/
@[expose] noncomputable def quantumRotation {N M : ℕ} (Q : Position ≃ₗᵢ[ℝ] Position) :
    QuantumConfiguration N M ≃ₗᵢ[ℝ] QuantumConfiguration N M :=
  LinearIsometryEquiv.withLpProdCongr 2 (configurationRotation Q) (configurationRotation Q)

/-- Translation of all spatial coordinates in the joint configuration. -/
@[expose] def quantumShift (N M : ℕ) (c : Position) : QuantumConfiguration N M :=
  toLp 2 (configurationShift N c, configurationShift M c)

/-- The simultaneous affine isometry `X ↦ quantumRotation Q X + quantumShift N M c`. -/
@[expose] noncomputable def quantumRigidMotion {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    QuantumConfiguration N M ≃ᵃⁱ[ℝ] QuantumConfiguration N M :=
  (quantumRotation Q).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ (quantumShift N M c))

@[simp] theorem quantumRigidMotion_symm_apply {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (X : QuantumConfiguration N M) :
    (quantumRigidMotion Q c).symm X =
      (quantumRotation Q).symm (X - quantumShift N M c) := rfl

/-- The joint motion as a measurable equivalence, for inverse changes of variables. -/
@[expose] noncomputable def quantumRigidMotionMeasurableEquiv {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    QuantumConfiguration N M ≃ᵐ QuantumConfiguration N M :=
  (quantumRigidMotion Q c).toHomeomorph.toMeasurableEquiv

theorem measurePreserving_quantumRigidMotion {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    MeasurePreserving (quantumRigidMotion (N := N) (M := M) Q c) volume volume :=
  (measurePreserving_add_right volume (quantumShift N M c)).comp
    (quantumRotation Q).measurePreserving

theorem measurePreserving_quantumRigidMotion_symm {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) :
    MeasurePreserving (quantumRigidMotion (N := N) (M := M) Q c).symm volume volume := by
  exact (measurePreserving_quantumRigidMotion Q c).symm
    (quantumRigidMotionMeasurableEquiv Q c)

@[simp] theorem particlePosition_quantumRigidMotion_fst {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (X : QuantumConfiguration N M) (i : Fin N) :
    particlePosition (quantumRigidMotion Q c X).fst i = Q (particlePosition X.fst i) + c := rfl

@[simp] theorem particlePosition_quantumRigidMotion_snd {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (X : QuantumConfiguration N M) (k : Fin M) :
    particlePosition (quantumRigidMotion Q c X).snd k = Q (particlePosition X.snd k) + c := rfl

/-- Simultaneous motions commute with electron permutations. -/
theorem quantumRigidMotion_symm_electron_permutation {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (σ : Equiv.Perm (Fin N))
    (X : QuantumConfiguration N M) :
    (quantumRigidMotion Q c).symm (toLp 2 (permutePositions σ X.fst, X.snd)) =
      toLp 2 (permutePositions σ ((quantumRigidMotion Q c).symm X).fst,
        ((quantumRigidMotion Q c).symm X).snd) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · ext ia
    rfl
  · rfl

/-- Simultaneous motions commute with nuclear permutations. -/
theorem quantumRigidMotion_symm_nuclear_permutation {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (τ : Equiv.Perm (Fin M))
    (X : QuantumConfiguration N M) :
    (quantumRigidMotion Q c).symm (toLp 2 (X.fst, permutePositions τ X.snd)) =
      toLp 2 (((quantumRigidMotion Q c).symm X).fst,
        permutePositions τ ((quantumRigidMotion Q c).symm X).snd) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · ext ia
    rfl

/-- Forward simultaneous motions commute with electron permutations. -/
theorem quantumRigidMotion_electron_permutation {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (σ : Equiv.Perm (Fin N))
    (X : QuantumConfiguration N M) :
    quantumRigidMotion Q c (toLp 2 (permutePositions σ X.fst, X.snd)) =
      toLp 2 (permutePositions σ (quantumRigidMotion Q c X).fst,
        (quantumRigidMotion Q c X).snd) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · ext ia
    rfl
  · rfl

/-- Forward simultaneous motions commute with nuclear permutations. -/
theorem quantumRigidMotion_nuclear_permutation {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (τ : Equiv.Perm (Fin M))
    (X : QuantumConfiguration N M) :
    quantumRigidMotion Q c (toLp 2 (X.fst, permutePositions τ X.snd)) =
      toLp 2 ((quantumRigidMotion Q c X).fst,
        permutePositions τ (quantumRigidMotion Q c X).snd) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rfl
  · ext ia
    rfl

end LiebThirring
end
