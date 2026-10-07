/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalPackingGeometry
public import LiebThirring.ThermoLimit.InterpolationContinuity
import Mathlib.Tactic

/-!
# Canonical ball energy densities and their seed

Canonical recurrence's standard sequence and the local seed estimate used at the
zero-density endpoint in limit convexity.
-/

@[expose] public section

open Metric Set

namespace LiebThirring.ThermoLimit

/-- The interpolated neutral energy in the standard centered ball. -/
noncomputable def canonicalInterpolated (E : Set Position → ℕ → ℝ)
    (j : ℕ) (x : ℝ) : ℝ := interpolate (E (ball (0 : Position) ((28 : ℝ) ^ j))) x

/-- The canonical ball sequence, including its explicitly inflated seed. -/
noncomputable def canonicalBallSequence (E : Set Position → ℕ → ℝ) (ρ : ℝ) (k : ℕ) : ℝ :=
  standardSequence (canonicalInterpolated E) ballVolumeConstant ρ k

theorem canonicalBallSequence_continuousOn (E : Set Position → ℕ → ℝ) (k : ℕ) :
    ContinuousOn (fun ρ => canonicalBallSequence E ρ k) (Ici 0) := by
  exact standardSequence_continuousOn ballVolumeConstant_pos.le
    (fun j => continuousOn_interpolate _) k

theorem canonicalBallSequence_lower_bound {E : Set Position → ℕ → ℝ} {A : ℝ}
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) :
    -A * ρ ≤ canonicalBallSequence E ρ (k + 1) := by
  apply standardSequence_lower_bound ballVolumeConstant_pos hρ
  intro j x hx
  exact neg_mul_le_interpolate_of_nat _ A
    (fun m => hlower _ m (pow_pos (by norm_num) _)) hx

theorem canonicalBallSequence_vacuum {E : Set Position → ℕ → ℝ}
    (hvacuum : ∀ L, 0 < L → E (ball (0 : Position) L) 0 = 0) (k : ℕ) :
    canonicalBallSequence E 0 k = 0 := by
  apply standardSequence_vacuum
  intro j
  rw [canonicalInterpolated]
  simpa only [Nat.cast_zero] using
    (interpolate_nat (E (ball (0 : Position) ((28 : ℝ) ^ j))) 0).trans
      (hvacuum _ (pow_pos (by norm_num : (0 : ℝ) < 28) j))

/-- The seed gives the exact linear upper envelope near vacuum. -/
theorem canonicalBallSequence_seed_small {E : Set Position → ℕ → ℝ}
    (hvacuum : E (ball (0 : Position) 1) 0 = 0) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) (1 / (28 * ballVolumeConstant))) :
    (1 / 28 : ℝ) * canonicalBallSequence E ρ 0 =
      ρ * E (ball (0 : Position) 1) 1 := by
  have hx : 28 * ρ * ballVolumeConstant ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) hρ.1) ballVolumeConstant_pos.le
    · have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 28)
        ballVolumeConstant_pos)).mp hρ.2
      nlinarith only [hh]
  simp only [canonicalBallSequence, standardSequence, standardBudget_zero,
    standardVolume_zero, canonicalInterpolated, pow_zero]
  rw [interpolate_eq_mul_of_mem_Icc_zero_one _ hx hvacuum]
  field_simp [ballVolumeConstant_pos.ne']

end LiebThirring.ThermoLimit

end
