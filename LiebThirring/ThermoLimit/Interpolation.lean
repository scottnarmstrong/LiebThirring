/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Linear interpolation of an energy indexed by particle number

This module interpolates integer particle sectors in the thermodynamic limit. Its lemmas carry the physical hypothesis that the argument is nonnegative.
-/

@[expose] public section

namespace LiebThirring.ThermoLimit

/-- The natural floor used on the physical half-line. -/
noncomputable def natFloor (x : ℝ) : ℕ := ⌊x⌋.toNat

/-- Linear interpolation of a sequence between consecutive natural numbers. -/
noncomputable def interpolate (F : ℕ → ℝ) (x : ℝ) : ℝ :=
  let n := natFloor x
  (1 - (x - n)) * F n + (x - n) * F (n + 1)

@[simp] theorem interpolate_nat (F : ℕ → ℝ) (n : ℕ) : interpolate F n = F n := by
  simp [interpolate, natFloor]

/-- On each unit interval, `interpolate` is the usual affine combination. -/
theorem interpolate_eq_of_mem_Ico (F : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ)) :
    interpolate F x = (1 - (x - n)) * F n + (x - n) * F (n + 1) := by
  have hfloor : natFloor x = n := by
    have hnonneg : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr ((Nat.cast_nonneg n).trans hx.1)
    have hi : ⌊x⌋ = (n : ℤ) := by
      apply Int.floor_eq_iff.mpr
      exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
    simp [natFloor, hi]
  simp [interpolate, hfloor]

/-- Closed-interval version, including the shared right endpoint. -/
theorem interpolate_eq_of_mem_Icc (F : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    interpolate F x = (1 - (x - n)) * F n + (x - n) * F (n + 1) := by
  rcases hx.2.eq_or_lt with h | h
  · subst x
    convert interpolate_nat F (n + 1) using 1 <;> norm_num
  · exact interpolate_eq_of_mem_Ico F n ⟨hx.1, h⟩

/-- The interpolation parameter belongs to `[0,1]`. -/
theorem sub_floor_mem_Icc {x : ℝ} (hx : 0 ≤ x) :
    x - (natFloor x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hfloor_nonneg : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hcast : ((natFloor x : ℕ) : ℝ) = (⌊x⌋ : ℤ) := by
    have hz : (⌊x⌋.toNat : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg hfloor_nonneg
    exact_mod_cast hz
  constructor
  · rw [hcast]
    exact sub_nonneg.mpr (Int.floor_le x)
  · rw [hcast]
    exact sub_le_iff_le_add.mpr (by simpa [add_comm] using (Int.lt_floor_add_one x).le)

/-- A linear lower bound on the integer values passes to the interpolated function. -/
theorem neg_mul_le_interpolate_of_nat (F : ℕ → ℝ) (A : ℝ)
    (hF : ∀ n, -A * n ≤ F n) {x : ℝ} (hx : 0 ≤ x) :
    -A * x ≤ interpolate F x := by
  let n := natFloor x
  let t := x - (n : ℝ)
  have ht := sub_floor_mem_Icc hx
  have h0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have h1 : 0 ≤ t := ht.1
  have hn := hF n
  have hn1 := hF (n + 1)
  rw [show interpolate F x = (1 - t) * F n + t * F (n + 1) by
    simp only [interpolate, n, t]]
  have hcomb := add_le_add (mul_le_mul_of_nonneg_left hn h0)
    (mul_le_mul_of_nonneg_left hn1 h1)
  calc
    -A * x = (1 - t) * (-A * (n : ℝ)) + t * (-A * ((n + 1 : ℕ) : ℝ)) := by
      dsimp [t]
      push_cast
      ring
    _ ≤ (1 - t) * F n + t * F (n + 1) := hcomb

/-- On the first unit interval, interpolation from the vacuum is multiplication by `x`. -/
theorem interpolate_eq_mul_of_mem_Icc_zero_one (F : ℕ → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hF0 : F 0 = 0) : interpolate F x = x * F 1 := by
  rw [interpolate_eq_of_mem_Icc F 0]
  · simp [hF0]
  · simpa using hx

end LiebThirring.ThermoLimit

end
