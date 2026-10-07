/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumState
public import LiebThirring.Defs.Antisymmetric

/-! # Electron statistics for joint states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Electron position and spin permutations act with the fermionic sign. -/
@[expose] def quantum_antisymmetric {N M q : ℕ} (ψ : QuantumState N M q) : Prop :=
  ∀ σ : Equiv.Perm (Fin N),
    ∀ᵐ X ∂(volume : Measure (QuantumConfiguration N M)),
      ∀ s : SpinLabels N q,
        ψ (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ X s

end LiebThirring

end
