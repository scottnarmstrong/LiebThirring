/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoHeadline.PhysicalEnergy
public import LiebThirring.ThermoBounds.Energy
public import LiebThirring.Thermodynamic.BallVolumeEq

/-!
# Actual volume and finite extended-real normalization

The proved ball measure identity identifies the normalization of the
arbitrary-radius limits with `ballVolume`. Region
finiteness is consumed before converting the physical energy from `EReal`
to its real value. Thus neither infinite endpoint can be masked by `toReal`.
-/

public section

open Metric MeasureTheory
open scoped NNReal
open LiebThirring.ThermoBounds

namespace LiebThirring.ThermoHeadline

theorem neutralBallVolume_eq_ballVolume (L : {L : ℝ // 0 < L}) :
    neutralBallVolume L.val = ballVolume L := by
  have hv := ballVolume_eq_volume L
  have hh := congrArg ENNReal.toReal hv.1
  rw [ENNReal.toReal_ofReal hv.2.le] at hh
  exact (neutralBallVolume_eq_volume L.property.le).trans hh.symm

/-- Exact equality of the normalized extended-real energy and the
coercion of the normalized physical real energy, using finiteness. -/
theorem confined_normalized_eq_coe_neutralBallDensity
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) (n : ℕ) :
    confinedGroundStateEnergy (z * n) n q z mass L / (ballVolume L : EReal) =
      (neutralBallDensity (physicalNeutralEnergy q z mass) L.val n : EReal) := by
  unfold neutralBallDensity
  rw [EReal.coe_div, neutralBallVolume_eq_ballVolume,
    coe_physicalNeutralEnergy q hq z hz mass _ n isOpen_ball
      (nonempty_ball.mpr L.property), dirichletRegionGroundStateEnergy_ball]

end LiebThirring.ThermoHeadline

end
