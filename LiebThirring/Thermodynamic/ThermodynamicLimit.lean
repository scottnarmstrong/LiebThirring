/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy
public import LiebThirring.Thermodynamic.BallVolume
public import Mathlib.Topology.Order.Real
import LiebThirring.Proofs.ThermodynamicLimit

/-! # All-sequence canonical zero-temperature thermodynamic limit -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

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
  by exact LiebThirring.Proofs.exists_unique_thermodynamic_energy_density q hq z hz m

end LiebThirring

end
