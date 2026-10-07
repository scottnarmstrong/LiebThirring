/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumState

/-! # Bosonic spinless nuclear statistics -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Nucleus permutations have positive sign and do not act on electron spins. -/
@[expose] def nuclear_symmetric {N M q : ℕ} (ψ : QuantumState N M q) : Prop :=
  ∀ τ : Equiv.Perm (Fin M),
    ∀ᵐ X ∂(volume : Measure (QuantumConfiguration N M)),
      ∀ s : SpinLabels N q,
        ψ (toLp 2 (X.fst, permutePositions τ X.snd)) s = ψ X s

end LiebThirring

end
