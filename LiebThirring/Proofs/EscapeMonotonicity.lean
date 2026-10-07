/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
import LiebThirring.Ionization.EscapeComparison
import LiebThirring.Ionization.EscapeOne

/-!
# Atomic energy decreases when an electron escapes

Compact form-core approximation and a remote-orbital wedge add one electron
with arbitrarily small energy cost. Source: Lieb (1984), equation (2.8).
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- Sending a normalized electron orbital to infinity lowers the atomic variational
threshold. The vacuum and one-electron sectors are handled separately. -/
theorem atomicGroundStateEnergy_le_pred (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) :
    atomicGroundStateEnergy N q Z ≤ atomicGroundStateEnergy (N - 1) q Z := by
  cases N with
  | zero => exact le_rfl
  | succ n =>
    cases n with
    | zero => exact atomicGroundStateEnergy_one_le_vacuum q hq Z
    | succ k => exact escape_atomicGroundStateEnergy_succ_le q hq (k + 1) Z

end LiebThirring.Proofs

end
