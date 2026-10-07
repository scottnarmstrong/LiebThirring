/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Energy

/-! # Relaxed-mass electronic Thomas–Fermi infimum -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The separately named honest infimum with mass at most ν. -/
@[expose] noncomputable def tfRelaxedEnergy {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) : EReal :=
  ⨅ ρ : {ρ : TFDensity // tfMass ρ ≤ (ν : ℝ)},
    (tfFunctional a z R ρ.val : EReal)

end LiebThirring

end
