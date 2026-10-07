/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy
import LiebThirring.Proofs.RelaxedMinimizer

/-! # Unique relaxed TF minimizer -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Relaxed attainment holds at every mass cap; no chosen minimizer is defined. -/
theorem exists_unique_tfRelaxedMinimizer {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∃! ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) ∧
      (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R :=
  by exact LiebThirring.Proofs.exists_unique_tfRelaxedMinimizer a ν z R

end LiebThirring

end
