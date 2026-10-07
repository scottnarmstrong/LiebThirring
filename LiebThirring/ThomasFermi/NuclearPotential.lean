/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-! # Positive molecular nuclear potential -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Positive nuclear potential; the value at each pole is immaterial to Lebesgue integrals. -/
@[expose] noncomputable def tfNuclearPotential {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) : ℝ :=
  ∑ k : Fin M, (z k : ℝ) / ‖x - R k‖

end LiebThirring

end
