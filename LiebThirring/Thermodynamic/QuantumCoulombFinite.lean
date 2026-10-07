/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumFormDomain
public import LiebThirring.Thermodynamic.QuantumRepulsionEnergy
public import LiebThirring.Thermodynamic.QuantumAttractionEnergy
import LiebThirring.Proofs.QuantumCoulombFinite

/-! # Joint pair-form finiteness -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem quantum_coulomb_lt_top {N M q : ℕ} (z : ℕ)
    (ψ : QuantumFormDomain N M q) :
    quantumRepulsionEnergy z ψ.val < ⊤ ∧
      quantumAttractionEnergy z ψ.val < ⊤ :=
  by exact LiebThirring.Proofs.quantum_coulomb_lt_top z ψ

end LiebThirring

end
