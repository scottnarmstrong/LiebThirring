/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumState

/-! # Joint Fourier kinetic energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The gradient-square normalization uses the Fourier multiplier (2π)². -/
@[expose] noncomputable def quantumElectronKineticEnergy {N M q : ℕ}
    (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ.fst‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (QuantumConfiguration N M)
        (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

end LiebThirring

end
