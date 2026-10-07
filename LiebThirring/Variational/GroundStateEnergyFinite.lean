/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy
import LiebThirring.Proofs.GroundStateEnergyFinite

/-! # Finite variational ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Fixed distinct nuclei and nonempty spin space give a finite real ground energy. -/
theorem groundStateEnergy_ne_top_ne_bot (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) :
    groundStateEnergy N q M z R hR ≠ ⊤ ∧
      groundStateEnergy N q M z R hR ≠ ⊥ :=
  by exact LiebThirring.Proofs.groundStateEnergy_ne_top_ne_bot q hq N M z R hR

end LiebThirring

end
