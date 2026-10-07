/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# One-particle density

The spatial density obtained by integrating out all other particle coordinates and summing over
particles.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

@[expose] noncomputable def density {N q : ℕ} (ψ : State N q) (x : Position) : ℝ≥0∞ :=
  ∑ i : Fin N, ∫⁻ y : OtherConfiguration i,
    (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2

end LiebThirring

end
