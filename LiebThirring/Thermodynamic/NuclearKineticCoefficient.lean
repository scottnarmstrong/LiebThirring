/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Basic.NNReal.Basic

/-! # Finite nuclear mass in electronic kinetic units -/

public section

open scoped NNReal

namespace LiebThirring

/-- Nuclear mass measured in electron masses; electron kinetic coefficient is one. -/
@[expose] noncomputable def nuclearKineticCoefficient
    (m : {m : ℝ≥0 // 0 < m}) : ℝ≥0 :=
  m.val⁻¹

end LiebThirring

end
