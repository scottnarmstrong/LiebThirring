/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-! # Three-dimensional ball volume -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The literal Euclidean ball volume formula, on positive radii. -/
@[expose] noncomputable def ballVolume (L : {L : ℝ // 0 < L}) : ℝ :=
  (4 * Real.pi / 3) * L.val ^ 3

end LiebThirring

end
