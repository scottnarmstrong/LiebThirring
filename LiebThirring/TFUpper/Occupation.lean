/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FilledModes

/-! # Floor occupations and their bounded particle deficit

The number put in cube `b` is literally `⌊α m_b⌋₊`. Summing the
remainders bounds the missing particles by the number of positive-mass
cubes, independently of the large-charge parameter. Source: Lieb–Simon (1977) III.5 (76), pp. 72–73. The deficit calculation is
direct proof.
-/

@[expose] public section
open scoped NNReal
namespace LiebThirring.TFUpper

/-- Particle occupation of a cube of prescribed TF mass. -/
noncomputable def cubeOccupation (α m : ℝ≥0) : ℕ := ⌊(α : ℝ) * (m : ℝ)⌋₊

/-- Total number of occupied modes in a finite mesh. -/
noncomputable def occupationCount {B : ℕ} (α : ℝ≥0) (m : Fin B → ℝ≥0) : ℕ :=
  ∑ b, cubeOccupation α (m b)

theorem cubeOccupation_le (α m : ℝ≥0) :
    (cubeOccupation α m : ℝ) ≤ (α : ℝ) * (m : ℝ) :=
  Nat.floor_le (mul_nonneg α.property m.property)

theorem occupationCount_le {B : ℕ} (α : ℝ≥0) (m : Fin B → ℝ≥0) :
    (occupationCount α m : ℝ) ≤ (α : ℝ) * ∑ b, (m b : ℝ) := by
  simp only [occupationCount, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => cubeOccupation_le α (m b)

theorem occupationCount_le_particleNumber {B : ℕ} (α ν : ℝ≥0)
    (m : Fin B → ℝ≥0) (hm : ∑ b, (m b : ℝ) = (ν : ℝ))
    (N : ℕ) (hN : (N : ℝ) = (α : ℝ) * (ν : ℝ)) :
    occupationCount α m ≤ N := by
  apply Nat.cast_le (α := ℝ) |>.mp
  rw [hN, ← hm]
  exact occupationCount_le α m

/-- Select a genuine lowest-mode occupation, allowing partial degenerate shells. -/
noncomputable def filledDirichletModes (q : ℕ) (hq : 0 < q) (n : ℕ) :
    Finset (TFLattice.ModeIndex q) :=
  Classical.choose (TFLattice.exists_isFilled_dirichlet hq n)

theorem card_filledDirichletModes (q : ℕ) (hq : 0 < q) (n : ℕ) :
    (filledDirichletModes q hq n).card = n :=
  (Classical.choose_spec (TFLattice.exists_isFilled_dirichlet hq n)).1

theorem isFilled_filledDirichletModes (q : ℕ) (hq : 0 < q) (n : ℕ) :
    TFLattice.IsFilled TFLattice.IsDirichletIndex (filledDirichletModes q hq n) :=
  (Classical.choose_spec (TFLattice.exists_isFilled_dirichlet hq n)).2

/-- The literal sum of Dirichlet `-Δ` eigenvalues occupied in the mesh. -/
noncomputable def occupiedCubeKinetic {B : ℕ} (q : ℕ) (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (α : ℝ≥0) (m : Fin B → ℝ≥0) : ℝ :=
  ∑ b, ∑ p ∈ filledDirichletModes q hq (cubeOccupation α (m b)),
    TFLattice.cubeEigenvalue ℓ p

end LiebThirring.TFUpper
end
