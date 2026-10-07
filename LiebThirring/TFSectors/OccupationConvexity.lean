/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.SectorPairs

/-! # Convex occupation-number bounds

The `4/3` error moment of any occupation vector is bounded by the `4/3`
power of its total particle number. This is the uniform Neumann sector estimate error estimate
used with the Neumann eigenvalue-sum remainder.
-/

public section

open scoped BigOperators

namespace LiebThirring.TFSectors

theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Real.rpow_nonneg (le_refl (0 : ℝ)) _
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        _ ≤ f a ^ p + (∑ i ∈ s, f i) ^ p :=
          add_le_add le_rfl (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        _ ≤ _ := Real.add_rpow_le_rpow_add (hf a (Finset.mem_insert_self a s))
          (Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)) hp

/-- The sum of the `4/3` occupation errors is at most `N^(4/3)`. -/
theorem sum_sectorCount_rpow_four_thirds_le {N : ℕ}
    (b : Fin N → LatticeIndex) :
    ∑ β ∈ TFCoulomb.occupiedCubes b,
        (TFCoulomb.sectorCount b β : ℝ) ^ ((4 : ℝ) / 3) ≤
      (N : ℝ) ^ ((4 : ℝ) / 3) := by
  calc
    _ ≤ (∑ β ∈ TFCoulomb.occupiedCubes b,
        (TFCoulomb.sectorCount b β : ℝ)) ^ ((4 : ℝ) / 3) :=
      sum_rpow_le_rpow_sum _ _ (fun _ _ => Nat.cast_nonneg _) (by norm_num)
    _ = _ := by
      rw [← Nat.cast_sum, TFCoulomb.sum_sectorCount]

end LiebThirring.TFSectors

end
