/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.MassCompletion

/-! # Exact and relaxed TF infima agree

The proof adds the missing mass as a diffuse ball density on the actual
carrier. All added energy costs are proved to vanish in the library.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem tfEnergy_eq_tfRelaxedEnergy {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfEnergy a ν z R = tfRelaxedEnergy a ν z R :=
  TFFunctional.tfEnergy_eq_tfRelaxedEnergy_library a ν z R

end LiebThirring.Proofs

end
