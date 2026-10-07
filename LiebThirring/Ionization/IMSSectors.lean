/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSAlgebra
public import LiebThirring.Sobolev.WeakEnergy
public import LiebThirring.Variational.CompactMass
public import LiebThirring.Variational.FormFinite

/-! # The subset localization partition and its permutation symmetry

The sector products partition the mass and respect the permutations that
preserve each sector. The one-particle cutoff functions remain explicit parameters.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace LiebThirring
open Sobolev

/-- The literal product cutoff for an inside-particle subset. -/
@[expose] noncomputable def imsSectorWeight {N : ℕ} (χ η : Position → ℝ)
    (S : Finset (Fin N)) (x : Configuration N) : ℝ :=
  (∏ i ∈ S, χ (particlePosition x i)) * ∏ i ∈ Finset.univ \ S, η (particlePosition x i)

/-- The subset products form a square partition whenever the one-particle pair does. -/
theorem sum_imsSectorWeight_sq {N : ℕ} (χ η : Position → ℝ)
    (hpart : ∀ y, χ y ^ 2 + η y ^ 2 = 1) (x : Configuration N) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, imsSectorWeight χ η S x ^ 2) = 1 := by
  simp only [imsSectorWeight, mul_pow, ← Finset.prod_pow]
  rw [← Finset.prod_add]
  simp only [hpart, Finset.prod_const_one]

/-- Setwise-preserving particle permutations fix the corresponding sector multiplier. -/
theorem imsSectorWeight_permutePositions {N : ℕ} (χ η : Position → ℝ)
    (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i, i ∈ S ↔ σ i ∈ S) (x : Configuration N) :
    imsSectorWeight χ η S (permutePositions σ x) = imsSectorWeight χ η S x := by
  simp only [imsSectorWeight, particlePosition_permutePositions]
  congr 1
  · exact Finset.prod_equiv σ hσ (fun i _ => rfl)
  · have hcomp : ∀ i, i ∈ Finset.univ \ S ↔ σ i ∈ Finset.univ \ S := by
      intro i
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact not_congr (hσ i)
    exact Finset.prod_equiv σ hcomp (fun i _ => rfl)

end LiebThirring

end
