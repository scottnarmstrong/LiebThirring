/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.BallVolume
import LiebThirring.Proofs.DensitySequenceExists

/-! # Every nuclear density has a canonical sequence -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem exists_neutral_density_sequence (ρ : ℝ≥0) :
    ∃ (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
      Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun j => (M j : ℝ) / ballVolume (L j))
        Filter.atTop (nhds (ρ : ℝ)) :=
  by exact LiebThirring.Proofs.exists_neutral_density_sequence ρ

end LiebThirring

end
