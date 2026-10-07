/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Scaling

/-! # Exact molecular Thomas--Fermi scaling -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- Thomas--Fermi energy scales with exponent 7/3. -/
theorem tfEnergy_scaling {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (α : {α : ℝ≥0 // 0 < α}) :
    tfEnergy a (α.val * ν) (fun k => α.val * z k)
      (fun k => ((α.val : ℝ) ^ (-(1 : ℝ) / 3)) • R k) =
    (((α.val : ℝ) ^ ((7 : ℝ) / 3) : ℝ) : EReal) * tfEnergy a ν z R :=
  tfEnergy_scaling_library a ν z R α

end LiebThirring.Proofs

end
