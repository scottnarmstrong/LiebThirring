/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.RealEnergy
public import Mathlib.Data.EReal.Basic

/-! # Extended-real variational ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Infimum over all normalized form-domain states; an empty set has value `⊤`. -/
@[expose] noncomputable def groundStateEnergy (N q M : ℕ) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) : EReal :=
  ⨅ ψ : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1},
    (realEnergy z R hR ψ.val : EReal)

end LiebThirring

end
