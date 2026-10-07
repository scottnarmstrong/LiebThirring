/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# Adding one orbital by a finite wedge sum

The omitted coordinates are enumerated by swapping the selected coordinate
with zero and then retaining the successors. The sign of this swap gives
the same exterior product as the usual increasing-coordinate enumeration.
-/

public section

open WithLp

namespace LiebThirring

/-- The complex fermionic sign of a finite permutation. -/
@[expose] def escapePermutationSign {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℂ :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)

theorem escapePermutationSign_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    escapePermutationSign (σ * τ) = escapePermutationSign σ * escapePermutationSign τ := by
  simp only [escapePermutationSign, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]

theorem escapePermutationSign_sq {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    escapePermutationSign σ * escapePermutationSign σ = 1 := by
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
    (Int.units_mul_self (Equiv.Perm.sign σ))
  simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one,
    escapePermutationSign] using h

theorem escape_permutePositions_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N))
    (x : Configuration N) :
    permutePositions τ (permutePositions σ x) = permutePositions (σ * τ) x := by
  rfl

theorem escape_permuteSpins_mul {N q : ℕ} (σ τ : Equiv.Perm (Fin N))
    (s : SpinLabels N q) :
    permuteSpins τ (permuteSpins σ s) = permuteSpins (σ * τ) s := by
  rfl

/-- Delete the selected particle, enumerating the others by a swap with zero. -/
@[expose] def escapeOmitPositions {N : ℕ} (i : Fin (N + 1))
    (x : Configuration (N + 1)) : Configuration N :=
  toLp 2 (fun ja => x (Equiv.swap 0 i ja.1.succ, ja.2))

/-- Spin labels in the same omitted-particle order as `escapeOmitPositions`. -/
@[expose] def escapeOmitSpins {N q : ℕ} (i : Fin (N + 1))
    (s : SpinLabels (N + 1) q) : SpinLabels N q :=
  fun j => s (Equiv.swap 0 i j.succ)

/-- The signed contribution with particle `i` in the added orbital. -/
@[expose] def escapeWedgeTerm {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ)
    (h : Position → Fin q → ℂ) (i : Fin (N + 1))
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) : ℂ :=
  escapePermutationSign (Equiv.swap 0 i) *
    f (escapeOmitPositions i x) (escapeOmitSpins i s) * h (particlePosition x i) (s i)

/-- Exterior multiplication by one orbital with the normalized wedge coefficient. -/
@[expose] noncomputable def escapeWedge {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ)
    (h : Position → Fin q → ℂ)
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) : ℂ :=
  ((Real.sqrt (N + 1))⁻¹ : ℝ) * ∑ i, escapeWedgeTerm f h i x s

/-- The full, unnormalized signed permutation sum of an amplitude. -/
@[expose] noncomputable def escapeAlternatingSum {N q : ℕ}
    (g : Configuration N → SpinLabels N q → ℂ)
    (x : Configuration N) (s : SpinLabels N q) : ℂ :=
  ∑ τ : Equiv.Perm (Fin N), escapePermutationSign τ *
    g (permutePositions τ x) (permuteSpins τ s)

theorem escapeAlternatingSum_permute {N q : ℕ}
    (g : Configuration N → SpinLabels N q → ℂ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q) :
    escapeAlternatingSum g (permutePositions σ x) (permuteSpins σ s) =
      escapePermutationSign σ * escapeAlternatingSum g x s := by
  unfold escapeAlternatingSum
  simp only [escape_permutePositions_mul, escape_permuteSpins_mul]
  have ht (τ : Equiv.Perm (Fin N)) :
      escapePermutationSign τ * g (permutePositions (σ * τ) x) (permuteSpins (σ * τ) s) =
      escapePermutationSign σ * (escapePermutationSign (σ * τ) *
        g (permutePositions (σ * τ) x) (permuteSpins (σ * τ) s)) := by
    rw [escapePermutationSign_mul]
    calc
      _ = (escapePermutationSign σ * escapePermutationSign σ) *
        (escapePermutationSign τ * g (permutePositions (σ * τ) x)
          (permuteSpins (σ * τ) s)) := by
        rw [escapePermutationSign_sq, one_mul]
      _ = _ := by ring
  simp_rw [ht]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft σ)
    (fun τ => escapePermutationSign τ * g (permutePositions τ x) (permuteSpins τ s))

/-- The ordered tensor before exterior multiplication. -/
@[expose] def escapeWedgeSeed {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ) (h : Position → Fin q → ℂ)
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) : ℂ :=
  f (escapeOmitPositions 0 x) (escapeOmitSpins 0 s) * h (particlePosition x 0) (s 0)

theorem escapeOmitPositions_decompose {N : ℕ} (i : Fin (N + 1))
    (τ : Equiv.Perm (Fin N)) (x : Configuration (N + 1)) :
    escapeOmitPositions 0 (permutePositions (Equiv.Perm.decomposeFin.symm (i, τ)) x) =
      permutePositions τ (escapeOmitPositions i x) := by
  ext ja
  simp only [escapeOmitPositions, permutePositions, PiLp.toLp_apply,
    Equiv.swap_self, Equiv.refl_apply, Equiv.Perm.decomposeFin_symm_apply_succ]

theorem escapeOmitSpins_decompose {N q : ℕ} (i : Fin (N + 1))
    (τ : Equiv.Perm (Fin N)) (s : SpinLabels (N + 1) q) :
    escapeOmitSpins 0 (permuteSpins (Equiv.Perm.decomposeFin.symm (i, τ)) s) =
      permuteSpins τ (escapeOmitSpins i s) := by
  funext j
  simp only [escapeOmitSpins, permuteSpins, Equiv.swap_self, Equiv.refl_apply,
    Equiv.Perm.decomposeFin_symm_apply_succ]

theorem escapePermutationSign_decompose {N : ℕ} (i : Fin (N + 1))
    (τ : Equiv.Perm (Fin N)) :
    escapePermutationSign (Equiv.Perm.decomposeFin.symm (i, τ)) =
      escapePermutationSign (Equiv.swap 0 i) * escapePermutationSign τ := by
  have hs : Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (i, τ)) =
      Equiv.Perm.sign (Equiv.swap 0 i) * Equiv.Perm.sign τ := by
    have h := Equiv.Perm.decomposeFin.symm_sign i (1 : Equiv.Perm (Fin N))
    simp only [Equiv.Perm.decomposeFin_symm_of_one, map_one, mul_one] at h
    rw [Equiv.Perm.decomposeFin.symm_sign, h]
  simp only [escapePermutationSign, hs, Units.val_mul, Int.cast_mul]

theorem escapeWedgeSeed_decompose {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ) (h : Position → Fin q → ℂ)
    (hf : ∀ (τ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions τ x) (permuteSpins τ s) = escapePermutationSign τ * f x s)
    (i : Fin (N + 1)) (τ : Equiv.Perm (Fin N))
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) :
    escapePermutationSign (Equiv.Perm.decomposeFin.symm (i, τ)) *
        escapeWedgeSeed f h (permutePositions (Equiv.Perm.decomposeFin.symm (i, τ)) x)
          (permuteSpins (Equiv.Perm.decomposeFin.symm (i, τ)) s) =
      escapeWedgeTerm f h i x s := by
  unfold escapeWedgeSeed
  rw [escapeOmitPositions_decompose, escapeOmitSpins_decompose, hf,
    escapePermutationSign_decompose]
  have hp : particlePosition (permutePositions (Equiv.Perm.decomposeFin.symm (i, τ)) x) 0 =
      particlePosition x i := by
    ext a
    simp only [particlePosition, permutePositions, PiLp.toLp_apply,
      Equiv.Perm.decomposeFin_symm_apply_zero]
  rw [hp]
  simp only [permuteSpins, Equiv.Perm.decomposeFin_symm_apply_zero]
  unfold escapeWedgeTerm
  calc
    _ = (escapePermutationSign τ * escapePermutationSign τ) *
        (escapePermutationSign (Equiv.swap 0 i) *
          f (escapeOmitPositions i x) (escapeOmitSpins i s) * h (particlePosition x i) (s i)) := by
      ring
    _ = _ := by rw [escapePermutationSign_sq, one_mul]

/-- Grouping the alternating tensor by its orbital coordinate leaves `N!`
equal copies of each omitted-particle term. -/
theorem escapeAlternatingSum_seed {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ) (h : Position → Fin q → ℂ)
    (hf : ∀ (τ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions τ x) (permuteSpins τ s) = escapePermutationSign τ * f x s)
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) :
    escapeAlternatingSum (escapeWedgeSeed f h) x s =
      (N.factorial : ℂ) * ∑ i, escapeWedgeTerm f h i x s := by
  unfold escapeAlternatingSum
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := N)).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [escapeWedgeSeed_decompose f h hf]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- The finite omitted-particle sum is antisymmetric whenever its input is. -/
theorem escapeWedge_sum_permute {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ) (h : Position → Fin q → ℂ)
    (hf : ∀ (τ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions τ x) (permuteSpins τ s) = escapePermutationSign τ * f x s)
    (σ : Equiv.Perm (Fin (N + 1))) (x : Configuration (N + 1))
    (s : SpinLabels (N + 1) q) :
    (∑ i, escapeWedgeTerm f h i (permutePositions σ x) (permuteSpins σ s)) =
      escapePermutationSign σ * ∑ i, escapeWedgeTerm f h i x s := by
  apply mul_left_cancel₀ (show (N.factorial : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
  calc
    _ = escapeAlternatingSum (escapeWedgeSeed f h) (permutePositions σ x)
        (permuteSpins σ s) := (escapeAlternatingSum_seed f h hf _ _).symm
    _ = escapePermutationSign σ * escapeAlternatingSum (escapeWedgeSeed f h) x s :=
      escapeAlternatingSum_permute _ σ x s
    _ = _ := by rw [escapeAlternatingSum_seed f h hf]; ring

/-- Pointwise fermionic covariance of the normalized wedge, derived from
the original amplitude's covariance. -/
theorem escapeWedge_permute {N q : ℕ}
    (f : Configuration N → SpinLabels N q → ℂ) (h : Position → Fin q → ℂ)
    (hf : ∀ (τ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions τ x) (permuteSpins τ s) =
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) * f x s)
    (σ : Equiv.Perm (Fin (N + 1))) (x : Configuration (N + 1))
    (s : SpinLabels (N + 1) q) :
    escapeWedge f h (permutePositions σ x) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * escapeWedge f h x s := by
  unfold escapeWedge
  rw [escapeWedge_sum_permute f h hf]
  change _ = escapePermutationSign σ * _
  ring

end LiebThirring

end
