/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Antisymmetric states

Simultaneous spatial and spin permutation with the fermionic sign.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

@[expose] def antisymmetric {N q : ℕ} (ψ : State N q) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ᵐ x ∂(volume : Measure (Configuration N)),
    ∀ s : SpinLabels N q,
      ψ (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ x s

end LiebThirring

end
