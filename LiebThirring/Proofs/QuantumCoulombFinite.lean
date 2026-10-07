/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.HardyJoint

/-!
# Finite Coulomb expectations for the quantum nuclear model

Particlewise Hardy estimates bound electron–electron, nucleus–nucleus and
electron–nucleus expectations by the full kinetic form.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring.Proofs

theorem quantum_coulomb_lt_top {N M q : ℕ} (z : ℕ)
    (ψ : QuantumFormDomain N M q) :
    quantumRepulsionEnergy z ψ.val < ⊤ ∧
      quantumAttractionEnergy z ψ.val < ⊤ :=
  LiebThirring.quantum_coulombEnergy_lt_top z ψ

end LiebThirring.Proofs

end
