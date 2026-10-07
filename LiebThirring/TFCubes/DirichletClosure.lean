/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.PhysicalFormRestriction
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Dirichlet graph closure and zero extension

The Dirichlet H¹₀ graph is the graph-norm closure of the literal compact smooth
jets supported inside the open region. Coordinatewise indicator extension is
an isometry; on the core it recovers the global smooth jet, hence closedness
of the global weak graph proves extension of every Dirichlet graph element.
-/

@[expose] public section

open MeasureTheory TopologicalSpace LineDeriv
open scoped Distributions SchwartzMap ContDiff FourierTransform
open LiebThirring.Sobolev

namespace LiebThirring.TFCubes

/-- The existing weak-derivative slot equals the literal classical Schwartz derivative. -/
theorem schwartzCoordinateDerivativeL2_eq {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3) :
    schwartzCoordinateDerivativeL2 f a = (lineDerivOp (coordinateVector a) f).toLp 2 volume := by
  apply (hasWeakDerivative_schwartzCoordinateDerivativeL2 f a).unique
  rw [hasWeakDerivative_iff_fourier_eq_symbol]
  have hd : 𝓕 ((lineDerivOp (coordinateVector a) f).toLp 2 volume) =
      (𝓕 (lineDerivOp (coordinateVector a) f)).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq _
  have hu : 𝓕 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume := SchwartzMap.toLp_fourier_eq f
  filter_upwards [(𝓕 (lineDerivOp (coordinateVector a) f)).coeFn_toLp 2 volume,
    (𝓕 f).coeFn_toLp 2 volume] with ξ hg hf
  rw [hd, hu, hg, hf, fourier_lineDeriv_coordinate]

end LiebThirring.TFCubes

end
