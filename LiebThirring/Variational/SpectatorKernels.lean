/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesResidual
public import LiebThirring.Ionization.EscapePotential

/-!
# Exact Coulomb splitting at an arbitrary selected particle

An explicit ordering of the remaining particles transports the selected-zero
insertion identities to any selected coordinate. These are extended
nonnegative identities, valid even at collisions; no subtraction of infinite
quantities occurs. spectator disintegration uses their finite integrated real versions.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The permutation putting the selected particle first and the explicitly
ordered spectator particles at successor indices. -/
@[expose] def spectatorOrderingPermutation {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) : Equiv.Perm (Fin (N + 1)) where
  toFun := Fin.cases i (fun j => (e j).val)
  invFun j := if h : j = i then 0 else (e.symm ⟨j, h⟩).succ
  left_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp only [Fin.cases_succ, (e j).property, ↓reduceDIte]
      simp
  right_inv j := by
    dsimp only
    split_ifs with h
    · simpa using h.symm
    · simp only [Fin.cases_succ, Equiv.apply_symm_apply]

/-- Insert a position and an explicitly ordered residual configuration. -/
@[expose] noncomputable def spectatorInsert {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (x : Position) (y : Configuration N) :
    Configuration (N + 1) :=
  insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)

/-- Reindexing the residual spatial coordinates has the expected component formula. -/
theorem configurationReindex_apply {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (y : Configuration k) (j : Fin k) (a : Fin 3) :
    Sobolev.configurationReindexMeasurableEquiv e y (e j, a) = y (j, a) := by
  simp [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.piCongrLeft]
  exact Equiv.piCongrLeft_apply_apply _ _ _ (j, a)

/-- After the ordering permutation, insertion is the selected-zero insertion. -/
theorem permutePositions_spectatorInsert {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (x : Position) (y : Configuration N) :
    permutePositions (spectatorOrderingPermutation i e) (spectatorInsert i e x y) =
      escapeInsertPositions x y := by
  ext ja
  rcases ja with ⟨j, a⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · change insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y) (i, a) = x a
    simp [insertParticle]
  · change insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)
      ((e j).val, a) = y (j, a)
    simp only [insertParticle, PiLp.toLp_apply, (e j).property, ↓reduceDIte]
    exact configurationReindex_apply i e y j a

/-- Repulsion splits into residual repulsion and the selected particle's interactions. -/
theorem electronRepulsion_spectatorInsert {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (x : Position) (y : Configuration N) :
    electronRepulsion (spectatorInsert i e x y) = electronRepulsion y +
      ∑ j : Fin N, coulombKernel x (particlePosition y j) := by
  rw [← electronRepulsion_permutePositions (spectatorOrderingPermutation i e),
    permutePositions_spectatorInsert, electronRepulsion_escapeInsertPositions]

/-- Attraction splits into residual attraction and the selected particle's attraction. -/
theorem attraction_spectatorInsert {N M : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Position) (y : Configuration N) :
    attraction z R (spectatorInsert i e x y) = attraction z R y +
      ∑ k : Fin M, (z k : ℝ≥0∞) * coulombKernel x (R k) := by
  rw [← attraction_permutePositions (spectatorOrderingPermutation i e),
    permutePositions_spectatorInsert, attraction_escapeInsertPositions]

/-- Atomic attraction has exactly the selected term `Z / |x|`. -/
theorem attraction_spectatorInsert_atom {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (x : Position) (y : Configuration N) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) (spectatorInsert i e x y) =
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) y +
        (Z : ℝ≥0∞) * coulombKernel x 0 := by
  rw [attraction_spectatorInsert]
  simp

end LiebThirring
end
