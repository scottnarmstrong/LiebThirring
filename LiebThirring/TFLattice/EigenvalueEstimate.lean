/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FirstDirichlet
public import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-!
# Uniform sharp first-n cube eigenvalue sums

The coefficient is the exact tfKineticConstant for −Δ. The same error
constant works for Dirichlet and Neumann occupations, every positive side,
and arbitrary partial last shells. Translation is absent from the eigenvalue
formula. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

namespace LiebThirring.TFLattice

noncomputable def cubeEigenvalueErrorConstant (q : ℕ) : ℝ :=
  Real.pi ^ 2 * fermiMomentConstant q

theorem cubeEigenvalueErrorConstant_nonneg (q : ℕ) : 0 ≤ cubeEigenvalueErrorConstant q :=
  mul_nonneg (sq_nonneg _) (fermiMomentConstant_nonneg q)

/-- Scaling a sharp lattice-moment estimate to the actual cube eigenvalues. -/
theorem sum_cubeEigenvalue_error_le_of_moment {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (s : Finset (ModeIndex q))
    (hm : |(∑ p ∈ s, (squaredRadius p.1 : ℝ)) -
      (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5| ≤
      fermiMomentConstant q * (s.card : ℝ) ^ (4 / 3 : ℝ)) :
    |(∑ p ∈ s, cubeEigenvalue ℓ p) -
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ)| ≤
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  have hscale : 0 ≤ Real.pi ^ 2 * ℓ.val⁻¹ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hm hscale
  have he : (∑ p ∈ s, cubeEigenvalue ℓ p) -
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ) =
      (Real.pi ^ 2 * ℓ.val⁻¹ ^ 2) * ((∑ p ∈ s, (squaredRadius p.1 : ℝ)) -
        (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5) := by
    rw [sum_cubeEigenvalue]
    have hl : (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ) =
        (Real.pi ^ 2 * ((q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5)) * ℓ.val⁻¹ ^ 2 := by
      calc
        _ = ((tfKineticConstant ⟨q, hq⟩).val * (s.card : ℝ) ^ (5 / 3 : ℝ)) * ℓ.val⁻¹ ^ 2 := by ring
        _ = _ := by rw [fermiRadius_kinetic hq s.card]
    rw [hl, div_eq_mul_inv, ← inv_pow]
    ring
  rw [he, abs_mul, abs_of_nonneg hscale]
  unfold cubeEigenvalueErrorConstant
  nlinarith only [h]

/-- Sharp eigenvalue sums, Neumann first-n sums, with uniform q-dependent constant. -/
theorem sum_cubeEigenvalue_neumann_error_le {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled (fun _ => True) s) :
    |(∑ p ∈ s, cubeEigenvalue ℓ p) -
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ)| ≤
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (4 / 3 : ℝ) :=
  sum_cubeEigenvalue_error_le_of_moment hq ℓ s (first_neumann_moment_error_le hq hs)

/-- Sharp eigenvalue sums, Dirichlet first-n sums, including arbitrary last-shell choices. -/
theorem sum_cubeEigenvalue_dirichlet_error_le {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) :
    |(∑ p ∈ s, cubeEigenvalue ℓ p) -
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ)| ≤
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (4 / 3 : ℝ) :=
  sum_cubeEigenvalue_error_le_of_moment hq ℓ s (first_dirichlet_moment_error_le hq hs)

/-- The exact lower-bound interface consumed by TFSectors. -/
theorem sum_cubeEigenvalue_neumann_lower {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled (fun _ => True) s) :
    (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ) -
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (4 / 3 : ℝ) ≤
        ∑ p ∈ s, cubeEigenvalue ℓ p := by
  have h := (abs_le.mp (sum_cubeEigenvalue_neumann_error_le hq ℓ hs)).1
  linarith only [h]

/-- The exact upper-bound interface for filled Dirichlet trials. -/
theorem sum_cubeEigenvalue_dirichlet_upper {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) :
    (∑ p ∈ s, cubeEigenvalue ℓ p) ≤
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (5 / 3 : ℝ) +
        cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  have h := (abs_le.mp (sum_cubeEigenvalue_dirichlet_error_le hq ℓ hs)).2
  linarith only [h]

end LiebThirring.TFLattice

end
