/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity

/-! # Sharp semiclassical kinetic constant -/

public section

open scoped ENNReal NNReal

namespace LiebThirring

/-- The sharp −Δ semiclassical coefficient for a fixed positive spin multiplicity. -/
@[expose] noncomputable def tfKineticConstant (q : {q : ℕ // 1 ≤ q}) : {a : ℝ // 0 < a} :=
  ⟨(3 / 5 : ℝ) * (6 * Real.pi ^ 2 / (q.val : ℝ)) ^ ((2 : ℝ) / 3), by
    have hq : (0 : ℝ) < (q.val : ℝ) := by
      have : 0 < q.val := q.property
      exact_mod_cast this
    positivity⟩

end LiebThirring

end
