/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.DirichletBallFormDomain
import LiebThirring.Proofs.ConfinedTrialExists

/-! # Nonempty confined sectors -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem exists_normalized_dirichlet_ball_form_domain (N M q : ℕ) (hq : 1 ≤ q)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    ∃ ψ : DirichletBallFormDomain N M q m L, ‖ψ.val.val‖ = 1 :=
  by exact LiebThirring.Proofs.exists_normalized_dirichlet_ball_form_domain N M q hq m L

end LiebThirring

end
