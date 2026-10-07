/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.IsDirichletBall

/-! # Confined joint form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The unnormalized Dirichlet form domain in a positive-radius ball. -/
@[expose] def DirichletBallFormDomain (N M q : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) : Type :=
  {ψ : QuantumFormDomain N M q // is_dirichlet_ball m L ψ.val}

attribute [reducible] DirichletBallFormDomain

end LiebThirring

end
