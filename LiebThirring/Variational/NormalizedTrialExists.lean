/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
import LiebThirring.Proofs.NormalizedTrialExists

/-! # Nonempty normalized form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- A normalized finite-kinetic-energy fermionic trial exists for every finite particle count. -/
theorem exists_normalized_formDomain (q : ℕ) (hq : 1 ≤ q) (N : ℕ) :
    ∃ ψ : FormDomain N q, ‖(ψ : State N q)‖ = 1 :=
  by exact LiebThirring.Proofs.exists_normalized_formDomain q hq N

end LiebThirring

end
