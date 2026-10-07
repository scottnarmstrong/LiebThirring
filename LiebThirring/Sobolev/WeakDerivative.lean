/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# Weak coordinate derivatives on the state carrier

The compact smooth test identity in the weak-derivative characterization uses the complex inner product,
conjugate-linear in the first slot. Neither normalization nor antisymmetry is required.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace LiebThirring.Sobolev

/-- The coordinate vector for a spatial component of a particle. -/
@[expose] noncomputable def coordinateVector {N : ℕ} (a : Fin N × Fin 3) : Configuration N :=
  EuclideanSpace.basisFun (Fin N × Fin 3) ℝ a

/-- The distributional coordinate derivative, tested against compact smooth spin amplitudes. -/
@[expose] def HasWeakDerivative {N q : ℕ} (a : Fin N × Fin 3) (u g : State N q) : Prop :=
  ∀ η : Configuration N → SpinAmplitudes N q,
    HasCompactSupport η → ContDiff ℝ ∞ η →
      (∫ x, inner ℂ (η x) (g x)) =
        -(∫ x, inner ℂ (fderiv ℝ η x (coordinateVector a)) (u x))

end LiebThirring.Sobolev

end
