/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
import LiebThirring.Variational.TrialConstruction

/-! # Normalized finite-energy trial states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- An antisymmetric form-domain state of norm one exists. -/
theorem exists_normalized_formDomain (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    ∃ ψ : FormDomain N q, ‖(ψ : State N q)‖ = 1 := by
  exact LiebThirring.exists_normalized_formDomain_trial q hq N

end LiebThirring.Proofs

end
