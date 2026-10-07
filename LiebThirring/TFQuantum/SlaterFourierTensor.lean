/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.FourierFactorIdentity

/-! # Fourier transport of arbitrary L² particle tensors

The existing full/partial Fourier factorization extends the Schwartz tensor
identity to arbitrary one-particle and spectator L² factors. This identity
does not assume H¹ membership or integrability of either factor.
direct proof transport through the proved
one-particle currying isometry.
-/

public section
open MeasureTheory
open scoped FourierTransform
namespace LiebThirring

/-- Full Fourier transformation factors on every actual inserted L² tensor. -/
theorem fourier_oneParticleInsertion {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : RestState i q) :
    𝓕 (oneParticleInsertion i f v) = oneParticleInsertion i (𝓕 f) (𝓕 v) := by
  apply (oneParticleCurryingLinearIsometryEquiv (q := q) i).injective
  change oneParticleCurrying i (𝓕 (oneParticleInsertion i f v)) =
    oneParticleCurrying i (oneParticleInsertion i (𝓕 f) (𝓕 v))
  let V := (restFourierLinearIsometryEquiv (q := q) i).toContinuousLinearEquiv.toContinuousLinearMap
  calc
    _ = V.compLp (𝓕 (oneParticleCurrying i (oneParticleInsertion i f v))) :=
      oneParticleCurrying_fourier i (oneParticleInsertion i f v)
    _ = V.compLp (𝓕 (tensorInsertion (H := RestState i q) f v)) :=
      congrArg (fun z => V.compLp (𝓕 z)) (oneParticleCurrying_insertion i f v)
    _ = V.compLp (tensorInsertion (H := RestState i q) (𝓕 f) v) :=
      congrArg V.compLp (fourier_tensorInsertion i f v)
    _ = tensorInsertion (H := RestState i q) (𝓕 f) (𝓕 v) :=
      restFourier_tensorInsertion i (𝓕 f) v
    _ = _ := (oneParticleCurrying_insertion i (𝓕 f) (𝓕 v)).symm

end LiebThirring
end
