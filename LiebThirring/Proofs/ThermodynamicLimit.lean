/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy
public import LiebThirring.Thermodynamic.BallVolume
import LiebThirring.ThermoHeadline.ConditionalHeadline
import LiebThirring.ThermoNeutral.ConditionalPacking

/-!
# Neutral thermodynamic energy density

Neutral cluster screening and variational packing give the canonical sequence limit.
Integer interpolation, convexity and complementary packings extend it to arbitrary
radii and counts, including density zero. Source: Lieb–Lebowitz (1972),
Theorems 3.1–3.2, 4.6 and 5.1.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring.Proofs

theorem exists_unique_thermodynamic_energy_density
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m}) :
    ∃! e : ℝ≥0 → ℝ,
      e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ : ℝ≥0) (t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤
          (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      ∀ (ρ : ℝ≥0) (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
        Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (M j : ℝ) / ballVolume (L j))
          Filter.atTop (nhds (ρ : ℝ)) →
        Filter.Tendsto
          (fun j => confinedGroundStateEnergy (z * M j) (M j) q z m (L j) /
            (ballVolume (L j) : EReal))
          Filter.atTop (nhds (e ρ : EReal)) :=
  LiebThirring.ThermoHeadline.exists_unique_thermodynamic_energy_density_of_neutral_packing
    q hq z hz m (LiebThirring.ThermoNeutral.physicalNeutralEnergy_neutral_packing q hq z hz m)

end LiebThirring.Proofs

end
