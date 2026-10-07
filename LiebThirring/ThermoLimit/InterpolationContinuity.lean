/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Interpolation
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Continuity of particle-number interpolation

Coupled integer interpolation's affine pieces agree at their endpoints. A locally finite closed
cover by unit intervals gives continuity on the entire physical half-line.
-/

public section

open Set

namespace LiebThirring.ThermoLimit

theorem locallyFinite_nat_unit_intervals :
    LocallyFinite (fun n : ℕ => Icc (n : ℝ) (n + 1 : ℝ)) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine ⟨Iio (N : ℝ), Iio_mem_nhds hN, ?_⟩
  apply (Set.finite_Iio N).subset
  rintro n ⟨y, ⟨hny, _⟩, hy⟩
  exact_mod_cast hny.trans_lt hy

theorem iUnion_nat_unit_intervals :
    (⋃ n : ℕ, Icc (n : ℝ) (n + 1 : ℝ)) = Ici (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hx⟩
    exact (Nat.cast_nonneg n).trans hx.1
  · intro hx
    have ht := sub_floor_mem_Icc hx
    exact mem_iUnion.mpr ⟨natFloor x, by constructor <;> linarith only [ht.1, ht.2]⟩

/-- The finite, piecewise affine energy interpolation is continuous on
nonnegative particle budgets, including the vacuum endpoint. -/
theorem continuousOn_interpolate (F : ℕ → ℝ) :
    ContinuousOn (interpolate F) (Ici 0) := by
  rw [← iUnion_nat_unit_intervals]
  apply locallyFinite_nat_unit_intervals.continuousOn_iUnion (fun _ => isClosed_Icc)
  intro n
  have hc : Continuous (fun x : ℝ => (1 - (x - n)) * F n + (x - n) * F (n + 1)) := by
    fun_prop
  exact hc.continuousOn.congr (fun x hx => interpolate_eq_of_mem_Icc F n hx)

end LiebThirring.ThermoLimit

end
