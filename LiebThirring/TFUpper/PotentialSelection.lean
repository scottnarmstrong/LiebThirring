/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteDensityBounds
public import LiebThirring.TFFunctional.PotentialNorm

/-! # Uniformly small potentials of the actual remote density

Fix a large near/far splitting radius to control the far part by the exact
mass. The remote density's Lp norm tends to zero under dilation, uniformly
in translation, so the near part vanishes. The translation can therefore
be selected afterwards to separate the remote and main supports.
direct proof.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap Topology
namespace LiebThirring.TFUpper

theorem eventually_remoteOrbitalDensity_potential_le {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (hn : (∫ x, ‖h x‖ ^ 2) = 1) (t : Fin q) (p : ℝ) (hp : 0 < p) :
    ∀ᶠ L : ℝ in atTop, ∀ hL : 0 < L, ∀ a : Position, ∀ x : Position,
      coulombPotential (tfDensityMeasure (remoteOrbitalDensity h hh t a L hL (r := r))) x ≤
        ENNReal.ofReal p := by
  let s : ℝ := 1 + 2 * (r : ℝ) / p
  have hs : 0 < s := by dsimp only [s]; positivity
  have hfar : (r : ℝ) / s ≤ p / 2 := by
    apply (div_le_iff₀ hs).mpr
    have hcancel : p * (2 * (r : ℝ) / p) = 2 * (r : ℝ) := by field_simp
    dsimp only [s]
    nlinarith only [hcancel, hp]
  let C : ℝ := (8 * Real.pi * Real.sqrt s) ^ ((2 : ℝ) / 5)
  let K : ℝ := ‖(remoteOrbitalDensity h hh t 0 1 zero_lt_one (r := r)).val‖
  have hpow : Tendsto (fun L : ℝ => L ^ (-(6 : ℝ) / 5)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 6 / 5)
  have hnear : Tendsto (fun L : ℝ => C * (L ^ (-(6 : ℝ) / 5) * K)) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hpow.mul_const K).const_mul C
  filter_upwards [hnear.eventually_lt_const (half_pos hp)] with L hsmall hL a x
  apply (TFFunctional.coulombPotential_tfDensityMeasure_le_norm
    (remoteOrbitalDensity h hh t a L hL (r := r)) x s hs).trans
  apply ENNReal.ofReal_le_ofReal
  rw [tfMass_remoteOrbitalDensity h hh hn t a L hL, norm_remoteOrbitalDensity]
  change C * (L ^ (-(6 : ℝ) / 5) * K) + (r : ℝ) / s ≤ p
  linarith only [hsmall, hfar]

end LiebThirring.TFUpper
end
