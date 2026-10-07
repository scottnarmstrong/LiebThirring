/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletOrbitals
public import LiebThirring.TFUpper.RemoteState

/-!
# Dirichlet cube orbitals

The literal zero-extended sine-product orbital is transported from physical
space to the one-particle configuration carrier. Its weak-gradient
construction and exact kinetic energy are proved in the companion kinetic
module. Proof: explicit cube spectral calculations and Slater upper bound, using the explicit
construction in cube spectral theory.
-/

public section

open MeasureTheory WithLp

namespace LiebThirring.TFUpper

/-- A normalized zero-extended Dirichlet cube mode on the one-particle
state carrier. -/
@[expose] noncomputable def dirichletCubeOrbital {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) : State 1 q :=
  spatialSpinToState q (dirichletCubeSpatialL2 ℓ b p)

/-- Pointwise representative of the spatial-to-L2 transport. -/
theorem spatialSpinToState_ae {q : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    ∀ᵐ X : Configuration 1 ∂volume,
      spatialSpinToState q f X =
        oneParticleSpinIsometry q (f (particlePosition X 0)) := by
  let h := spatialSpinLpIsometry q f
  have houter := Lp.coeFn_compMeasurePreserving h
    oneParticleConfigurationEquiv.symm.measurePreserving
  have hspin := (oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
    (map_zero (oneParticleSpinIsometry q)) f
  have hspin' := oneParticleConfigurationEquiv.symm.measurePreserving.quasiMeasurePreserving.ae
    hspin
  filter_upwards [houter, hspin'] with X hX hs
  change (Lp.compMeasurePreserving oneParticleConfigurationEquiv.symm
    oneParticleConfigurationEquiv.symm.measurePreserving h) X = _
  rw [hX]
  simp only [Function.comp_apply] at hs ⊢
  exact hs

/-- The state has the literal indicator-times-sine-product representative. -/
theorem dirichletCubeOrbital_ae {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    ∀ᵐ X : Configuration 1 ∂volume,
      dirichletCubeOrbital ℓ b p X =
        oneParticleSpinIsometry q
          ((TFCubes.cubeInterior b ℓ).indicator
            (TFCubes.dirichletCubeModeValue ℓ b p) (particlePosition X 0)) := by
  have hspatial := oneParticleConfigurationEquiv.symm.measurePreserving.quasiMeasurePreserving.ae
    (dirichletCubeSpatialL2_ae ℓ b p)
  filter_upwards [spatialSpinToState_ae (dirichletCubeSpatialL2 ℓ b p), hspatial]
    with X hX hspatialX
  have he : oneParticleConfigurationEquiv.symm X = particlePosition X 0 := by
    apply oneParticleConfigurationEquiv.injective
    rw [oneParticleConfigurationEquiv.apply_symm_apply]
    apply PiLp.ext
    intro ia
    obtain ⟨i, a⟩ := ia
    exact congrArg (fun j : Fin 1 => X (j, a)) (Subsingleton.elim i 0)
  rw [dirichletCubeOrbital, hX, ← he, hspatialX]

/-- The orbital-value representative is the literal zero-extended cube mode. -/
theorem orbitalValue_dirichletCubeOrbital_ae {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (t : Fin q) :
    ∀ᵐ x : Position ∂volume,
      orbitalValue (dirichletCubeOrbital ℓ b p) x t =
        (TFCubes.cubeInterior b ℓ).indicator
          (TFCubes.dirichletCubeModeValue ℓ b p) x t := by
  have h := oneParticleConfigurationEquiv.measurePreserving.quasiMeasurePreserving.ae
    (dirichletCubeOrbital_ae ℓ b p)
  filter_upwards [h] with x hx
  have hv := congrArg (fun v : SpinAmplitudes 1 q => v (oneParticleSpinLabel t)) hx
  have heval : oneParticleConfigurationEquiv x = oneParticleConfiguration x := rfl
  have hspin_eval (v : EuclideanSpace ℂ (Fin q)) :
      oneParticleSpinIsometry q v (oneParticleSpinLabel t) = v t := rfl
  simpa only [orbitalValue, heval, particlePosition_oneParticleConfiguration,
    hspin_eval] using hv

end LiebThirring.TFUpper

end
