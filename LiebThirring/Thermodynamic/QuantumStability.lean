/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumEnergy
import LiebThirring.Proofs.QuantumStability

/-! # Extensive stability with quantum nuclei -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem quantum_stability (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q),
        -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
          (nuclearKineticCoefficient m : ℝ) *
            (quantumNuclearKineticEnergy ψ.val).toReal ≤ quantumEnergy z m ψ :=
  by exact LiebThirring.Proofs.quantum_stability q hq z hz

end LiebThirring

end
