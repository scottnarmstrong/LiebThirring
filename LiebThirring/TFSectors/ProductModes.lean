/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.Indices
public import LiebThirring.Packing.LatticeGeometry
import LiebThirring.Kinetic.Permutation

/-!
# Literal Neumann product modes

These are the normalized cosine modes and the standard spin vectors from cube spectral theory,
tensorized over the assigned particles. Completeness and the physical diagonal
form identity are separate spectral inputs; permutation invariance is proved here.
-/

@[expose] public section
open scoped BigOperators
namespace LiebThirring.TFSectors

/-- The literal normalized translated cube cosine mode, with its spin vector. -/
noncomputable def neumannModeValue {q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (β : LatticeIndex) (p : TFLattice.ModeIndex q) (x : Position) (s : Fin q) : ℂ :=
  if s = p.2 then
    ((ℓ.val ^ (-(3 : ℝ) / 2) * ∏ a : Fin 3,
      (if p.1 a = 0 then 1 else Real.sqrt 2) *
        Real.cos (Real.pi * (p.1 a : ℝ) * (x a - ℓ.val * (β a : ℝ)) / ℓ.val)) : ℝ)
  else 0

/-- Tensor product of the literal one-particle Neumann spatial-and-spin modes. -/
noncomputable def neumannProductMode {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (k : Fin N → TFLattice.ModeIndex q)
    (x : Configuration N) : SpinAmplitudes N q :=
  WithLp.toLp 2 (fun s => ∏ i : Fin N, neumannModeValue ℓ (b i) (k i) (particlePosition x i) (s i))

theorem neumannProductMode_permute {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (k : Fin N → TFLattice.ModeIndex q)
    (σ : Equiv.Perm (Fin N)) (hb : ∀ i, b (σ i) = b i) (hk : ∀ i, k (σ i) = k i)
    (x : Configuration N) (s : SpinLabels N q) :
    neumannProductMode ℓ b k (permutePositions σ x) (permuteSpins σ s) =
      neumannProductMode ℓ b k x s := by
  change (∏ i : Fin N, neumannModeValue ℓ (b i) (k i)
      (particlePosition x (σ i)) (s (σ i))) = _
  calc
    _ = ∏ i : Fin N, neumannModeValue ℓ (b (σ i)) (k (σ i))
        (particlePosition x (σ i)) (s (σ i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hb i, hk i]
    _ = _ := Equiv.prod_comp σ (fun i => neumannModeValue ℓ (b i) (k i) (particlePosition x i) (s i))

theorem assignment_stable_swap {N : ℕ} {A : Type*} (b : Fin N → A)
    {i j : Fin N} (hij : b i = b j) : ∀ r, b (Equiv.swap i j r) = b r := by
  classical
  intro r
  by_cases hi : r = i
  · subst r
    simpa using hij.symm
  by_cases hj : r = j
  · subst r
    simpa using hij
  · rw [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem neumannProductMode_swap {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (k : Fin N → TFLattice.ModeIndex q)
    {i j : Fin N} (hb : b i = b j) (hk : k i = k j)
    (x : Configuration N) (s : SpinLabels N q) :
    neumannProductMode ℓ b k (permutePositions (Equiv.swap i j) x)
      (permuteSpins (Equiv.swap i j) s) = neumannProductMode ℓ b k x s :=
  neumannProductMode_permute ℓ b k _ (assignment_stable_swap b hb) (assignment_stable_swap k hk) x s

end LiebThirring.TFSectors
end
