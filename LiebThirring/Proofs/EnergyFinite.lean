/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.AttractionCoercivity

/-!
# Finite Thomas--Fermi energies
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- The exact and relaxed Thomas--Fermi energies are finite. -/
theorem tfEnergy_ne_top_ne_bot {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfEnergy a ν z R ≠ ⊤ ∧ tfEnergy a ν z R ≠ ⊥ ∧
      tfRelaxedEnergy a ν z R ≠ ⊤ ∧ tfRelaxedEnergy a ν z R ≠ ⊥ :=
  TFFunctional.tfEnergy_ne_top_ne_bot_library a ν z R

end LiebThirring.Proofs

end
