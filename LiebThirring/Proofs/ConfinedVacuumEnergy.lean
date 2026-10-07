/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.Vacuum

/-!
# Dirichlet ball vacuum energy

With no electrons or nuclei, the normalized vacuum has zero kinetic and Coulomb energy.
-/

public section

open scoped NNReal

namespace LiebThirring.Proofs

theorem confinedGroundStateEnergy_vacuum (q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy 0 0 q z m L = 0 :=
  LiebThirring.confinedGroundStateEnergy_vacuum_eq q z m L

end LiebThirring.Proofs

end
