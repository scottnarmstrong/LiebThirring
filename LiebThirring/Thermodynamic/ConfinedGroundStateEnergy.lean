/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.DirichletBallFormDomain
public import LiebThirring.Thermodynamic.QuantumEnergy
public import Mathlib.Data.EReal.Basic

/-! # Canonical confined ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Honest complete-order infimum: empty sectors give top, unbounded ones bottom. -/
@[expose] noncomputable def confinedGroundStateEnergy (N M q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) : EReal :=
  ⨅ ψ : {ψ : DirichletBallFormDomain N M q m L // ‖ψ.val.val‖ = 1},
    (quantumEnergy z m ψ.val.val : EReal)

end LiebThirring

end
