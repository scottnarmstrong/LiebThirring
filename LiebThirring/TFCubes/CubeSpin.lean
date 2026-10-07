/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Physical L² spin components

The finite spin Hilbert norm decomposes into the literal scalar L² component
norms, including an empty spin family. The decomposition uses the actual
Euclidean spin inner product, rather than the supremum norm of functions.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace LiebThirring.TFCubes

variable {X : Type*} [MeasurableSpace X] {q : ℕ}

/-- The squared physical L² norm is the physical integral of the squared pointwise norm. -/
theorem norm_sq_localL2 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (μ : Measure X) (u : Lp F 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm)

end LiebThirring.TFCubes

end
