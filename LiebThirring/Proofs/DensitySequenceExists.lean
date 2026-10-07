/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.BallVolume

/-!
# Neutral integer sectors at a prescribed density

Positive radii tending to infinity and rounded integer nuclear counts realize
every nonnegative nuclear density with exact electron neutrality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring.Proofs

/-- Every nonnegative density is approached by integer particle counts in
Euclidean balls whose radii tend to infinity. -/
theorem exists_neutral_density_sequence (ρ : ℝ≥0) :
    ∃ (L : ℕ → {L : ℝ // 0 < L}) (M : ℕ → ℕ),
      Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun j => (M j : ℝ) / LiebThirring.ballVolume (L j))
        Filter.atTop (nhds (ρ : ℝ)) := by
  let L : ℕ → {L : ℝ // 0 < L} := fun j => ⟨(j : ℝ) + 1, by positivity⟩
  let V : ℕ → ℝ := fun j => LiebThirring.ballVolume (L j)
  let M : ℕ → ℕ := fun j => ⌊(ρ : ℝ) * V j⌋₊
  refine ⟨L, M, ?_, ?_⟩
  · exact Filter.atTop.tendsto_atTop_add_const_right 1 tendsto_natCast_atTop_atTop
  · have hL : Filter.Tendsto (fun j => (L j).val) Filter.atTop Filter.atTop :=
      Filter.atTop.tendsto_atTop_add_const_right 1 tendsto_natCast_atTop_atTop
    have hV : Filter.Tendsto V Filter.atTop Filter.atTop := by
      dsimp [V, LiebThirring.ballVolume]
      have hpow : Filter.Tendsto (fun x : ℝ => x ^ 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop (by norm_num)
      exact Filter.Tendsto.const_mul_atTop (show 0 < (4 * Real.pi / 3 : ℝ) by positivity)
        (hpow.comp hL)
    exact (tendsto_nat_floor_mul_div_atTop ρ.coe_nonneg).comp hV

end LiebThirring.Proofs

end
