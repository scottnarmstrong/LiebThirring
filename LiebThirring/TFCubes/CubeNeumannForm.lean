/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeMixedBases
public import LiebThirring.TFCubes.CubeWeakCoefficients
public import LiebThirring.TFCubes.CubeSpinWeak
public import LiebThirring.TFCubes.CubeSpectralSum

/-! # The full physical one-particle Neumann cube form identity -/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace LiebThirring.TFCubes

/-- The complete mixed scalar basis has the actual compact-test limit representative. -/
theorem neumannMixedCubeScalarBasis_eq_testLimit {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (a : Fin 3)
    (p : NeumannMixedCubeModeIndex q a) :
    neumannMixedCubeScalarBasis ℓ b a p.1 =
      neumannCubeMixedTestLimitL2 ℓ b p.1.val a ⟨p.1.val a, p.1.property⟩ := by
  apply Lp.ext
  exact (neumannMixedCubeScalarBasis_ae ℓ b a p).trans
    ((neumannCubeMixedTestLimit_memLp ℓ b p.1.val a
      ⟨p.1.val a, p.1.property⟩).coeFn_toLp.symm)

end LiebThirring.TFCubes

end
