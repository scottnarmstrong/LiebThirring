/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumFormDomain
public import LiebThirring.Thermodynamic.NuclearKineticCoefficient
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Dirichlet ball confinement by form closure -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Approximation by symmetric compact smooth states in the full kinetic form norm. -/
@[expose] def is_dirichlet_ball {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : QuantumState N M q) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q),
      let φ : QuantumState N M q :=
        f.toLp 2 (volume : Measure (QuantumConfiguration N M))
      IsCompact (tsupport f) ∧
      tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
        Metric.ball (0 : Position) L.val) ∧
        (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)} ∧
      quantum_antisymmetric φ ∧ nuclear_symmetric φ ∧
      ENNReal.ofReal (‖ψ - φ‖ ^ 2) +
        quantumElectronKineticEnergy (ψ - φ) +
        (nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (ψ - φ) < ENNReal.ofReal ε

end LiebThirring

end
