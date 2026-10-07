/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterOneBodyAlgebra
public import LiebThirring.TFQuantum.SlaterMarginalsTwoBodyGeometry

/-! # The two surviving pairings and the literal complex exchange kernel -/

public section
open scoped ComplexConjugate
namespace LiebThirring

theorem sum_orthonormal_two_body_spectator {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (σ : Equiv.Perm (Fin N)) (i k : Fin N) (hik : i ≠ k)
    (x y : Position) :
    (∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ((orbitalContraction (u (σ i)) (u (τ i)) x *
          orbitalContraction (u (σ k)) (u (τ k)) y) *
          ∏ j : {j : Fin N // j ≠ i ∧ j ≠ k}, inner ℂ (u (σ j)) (u (τ j)))) =
      orbitalContraction (u (σ i)) (u (σ i)) x *
        orbitalContraction (u (σ k)) (u (σ k)) y -
      orbitalContraction (u (σ i)) (u (σ k)) x *
        orbitalContraction (u (σ k)) (u (σ i)) y := by
  classical
  simp only [orthonormal_iff_ite.mp hu]
  have hp (τ : Equiv.Perm (Fin N)) :
      (∏ j : {j : Fin N // j ≠ i ∧ j ≠ k}, if σ j = τ j then (1 : ℂ) else 0) =
        ∏ j ∈ (Finset.univ.erase i).erase k, if σ j = τ j then (1 : ℂ) else 0 :=
    (Finset.prod_subtype (p := fun j : Fin N => j ≠ i ∧ j ≠ k)
      ((Finset.univ.erase i).erase k) (by intro j; simp [and_comm])
      (fun j => if σ j = τ j then (1 : ℂ) else 0)).symm
  simp_rw [hp]
  have he := sum_permutation_two_body_contraction σ i k hik (fun τ =>
    orbitalContraction (u (σ i)) (u (τ i)) x *
      orbitalContraction (u (σ k)) (u (τ k)) y)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro τ _
  ring

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

/-- The exchanged contraction is the spin-summed squared modulus of the actual projector. -/
theorem sum_orbitalContraction_cross_eq_exchange {N q : ℕ} (u : Fin N → State 1 q)
    (x y : Position) :
    (∑ j : Fin N, ∑ k : Fin N,
      orbitalContraction (u j) (u k) x * orbitalContraction (u k) (u j) y) =
      (slaterExchangeDensity u x y : ℂ) := by
  classical
  simp only [orbitalContraction, slaterExchangeDensity, Complex.ofReal_sum,
    Complex.ofReal_pow, ← Complex.conj_mul', slaterDensityMatrix, map_sum,
    map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The full direct-minus-exchange contraction equals the prescribed pair density. -/
theorem sum_orbitalContraction_pair_eq_direct_sub_exchange {N q : ℕ}
    (u : Fin N → State 1 q) (x y : Position) :
    (∑ j : Fin N, ∑ k : Fin N,
      (orbitalContraction (u j) (u j) x * orbitalContraction (u k) (u k) y -
        orbitalContraction (u j) (u k) x * orbitalContraction (u k) (u j) y)) =
      ((slaterOrbitalDensity u x * slaterOrbitalDensity u y -
        slaterExchangeDensity u x y : ℝ) : ℂ) := by
  simp only [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul_sum, sum_orbitalContraction_self_eq_density,
    sum_orbitalContraction_self_eq_density, sum_orbitalContraction_cross_eq_exchange,
    Complex.ofReal_sub, Complex.ofReal_mul]

end LiebThirring
end
