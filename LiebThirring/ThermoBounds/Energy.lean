/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalSequence
import Mathlib.Tactic

/-!
# Neutral energies for arbitrary-radius comparisons

Throughout this packet `E Ω m` denotes the real neutral-sector infimum
`E(z*m,m;Ω)` at fixed physical parameters. These are literal normalized
energies, not a definition of the thermodynamic limit. The standard
sequence is exactly canonical recurrence, including its inflated seed.
-/

@[expose] public section

open Metric MeasureTheory
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

/-- Lebesgue volume of the ball of positive radius `L`. -/
noncomputable def neutralBallVolume (L : ℝ) : ℝ := ballVolumeConstant * L ^ 3

/-- Integer neutral energy divided by its actual ball volume. -/
noncomputable def neutralBallDensity (E : Set Position → ℕ → ℝ) (L : ℝ) (m : ℕ) : ℝ :=
  E (ball (0 : Position) L) m / neutralBallVolume L

/-- The canonical recurrence sequence, as a function of its scale index and density. -/
noncomputable def neutralStandardSequence (E : Set Position → ℕ → ℝ)
    (k : ℕ) (s : ℝ) : ℝ :=
  canonicalBallSequence E s k

theorem neutralBallVolume_pos {L : ℝ} (hL : 0 < L) : 0 < neutralBallVolume L :=
  mul_pos ballVolumeConstant_pos (pow_pos hL _)

theorem neutralBallVolume_eq_volume {L : ℝ} (hL : 0 ≤ L) :
    neutralBallVolume L = volume.real (ball (0 : Position) L) :=
  (volume_real_ball_position _ hL).symm

theorem neutralBallVolume_standard (k : ℕ) :
    neutralBallVolume ((28 : ℝ) ^ k) = standardVolume ballVolumeConstant k := by
  unfold neutralBallVolume standardVolume
  rw [← pow_mul]
  congr 2
  omega

/-- Positive scales use the physical density without seed inflation. -/
theorem neutralStandardSequence_eq {E : Set Position → ℕ → ℝ} {k : ℕ}
    (hk : 0 < k) (s : ℝ) :
    neutralStandardSequence E k s =
      interpolate (E (ball (0 : Position) ((28 : ℝ) ^ k)))
        (s * standardVolume ballVolumeConstant k) / standardVolume ballVolumeConstant k := by
  unfold neutralStandardSequence canonicalBallSequence standardSequence standardBudget
  rw [ite_eq_right (Nat.ne_of_gt hk), canonicalInterpolated]

/-- The extensive quantum stability lower bound at the exact integer target sector. -/
theorem neutralBallDensity_lower_bound {E : Set Position → ℕ → ℝ} {A : ℝ}
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    {L : ℝ} (hL : 0 < L) (m : ℕ) :
    -A * ((m : ℝ) / neutralBallVolume L) ≤ neutralBallDensity E L m := by
  unfold neutralBallDensity
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hlower L m hL) (neutralBallVolume_pos hL).le

end LiebThirring.ThermoBounds

end
