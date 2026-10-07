/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.TrialExists

/-!
# Normalized Dirichlet ball trials

Compact Slater electron states and symmetric nuclear states give normalized
finite-energy trials supported strictly inside a ball of positive radius.
-/

public section

open scoped NNReal

namespace LiebThirring.Proofs

theorem exists_normalized_dirichlet_ball_form_domain (N M q : ℕ) (hq : 1 ≤ q)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    ∃ ψ : DirichletBallFormDomain N M q m L, ‖ψ.val.val‖ = 1 :=
  LiebThirring.exists_normalized_dirichlet_ball_trial N M q hq m L

end LiebThirring.Proofs

end
