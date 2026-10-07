/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.PhysicalDensities
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-!
# The L² density estimate on the physical carrier

The real `lpNorm` is used together with a proved `MemLp` assertion, so the
estimate is an actual finite L² norm. Source: Lieb–Simon III.14, pp. 69–71.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring.TFLattice

theorem lpNorm_two_eq_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) hf.aestronglyMeasurable]
  have hp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp_rw [hp, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simpa only [one_div] using (Real.sqrt_eq_rpow (∫ x, f x ^ 2 ∂μ)).symm

theorem physicalFilledDensity_sub_eq_indicator {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q)) :
    (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) =
    (physicalCube ℓ b).indicator (fun x =>
      filledDensity ℓ s (cubeCoordinates b x) - s.card / ℓ.val ^ 3) := by
  classical
  ext x
  by_cases hx : x ∈ physicalCube ℓ b <;> simp [physicalFilledDensity, hx]

theorem memLp_physicalFilledDensity_sub_two {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q)) :
    MemLp (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) 2 volume := by
  rw [physicalFilledDensity_sub_eq_indicator,
    memLp_indicator_iff_restrict (measurableSet_physicalCube ℓ b)]
  exact (memLp_filledDensity_sub_two ℓ s).comp_measurePreserving
    (measurePreserving_cubeCoordinates_restrict ℓ b)

theorem lpNorm_physicalFilledDensity_sub_eq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q)) :
    lpNorm (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) 2 volume =
    lpNorm (fun x => filledDensity ℓ s x - s.card / ℓ.val ^ 3) 2 (cubeCoordinateMeasure ℓ) := by
  rw [physicalFilledDensity_sub_eq_indicator]
  unfold lpNorm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_physicalCube ℓ b)]
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving
    (memLp_filledDensity_sub_two ℓ s).aestronglyMeasurable
    (measurePreserving_cubeCoordinates_restrict ℓ b))

/-- Filled-density convergence's physical L² estimate, uniform in the translated cube and the
choice of modes inside a degenerate last shell. -/
theorem lpNorm_physicalFilledDensity_sub_le {q : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) :
    lpNorm (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) 2 volume ≤
      Real.sqrt (1944 * q / ℓ.val ^ 3) * (s.card : ℝ) ^ (5 / 6 : ℝ) := by
  rw [lpNorm_physicalFilledDensity_sub_eq,
    lpNorm_two_eq_sqrt_integral_sq (memLp_filledDensity_sub_two ℓ s)]
  exact sqrt_integral_filledDensity_sub_sq_le hq ℓ hs

end LiebThirring.TFLattice

end
