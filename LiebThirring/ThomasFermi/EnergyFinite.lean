/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy
import LiebThirring.Proofs.EnergyFinite

/-! # Finite exact and relaxed TF energies -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Both variational infima are finite; boundedness and nonemptiness are conclusions. -/
theorem tfEnergy_ne_top_ne_bot {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfEnergy a ν z R ≠ ⊤ ∧ tfEnergy a ν z R ≠ ⊥ ∧
      tfRelaxedEnergy a ν z R ≠ ⊤ ∧ tfRelaxedEnergy a ν z R ≠ ⊥ :=
  by exact LiebThirring.Proofs.tfEnergy_ne_top_ne_bot a ν z R

end LiebThirring

end
