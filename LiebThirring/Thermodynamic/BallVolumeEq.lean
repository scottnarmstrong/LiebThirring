/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.BallVolume
import LiebThirring.Proofs.BallVolumeEq

/-! # Ball measure and positive volume -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem ballVolume_eq_volume (L : {L : ℝ // 0 < L}) :
    ENNReal.ofReal (ballVolume L) = volume (Metric.ball (0 : Position) L.val) ∧
      0 < ballVolume L :=
  by exact LiebThirring.Proofs.ballVolume_eq_volume L

end LiebThirring

end
