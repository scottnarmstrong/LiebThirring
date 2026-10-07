/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterNorm
public import LiebThirring.TFQuantum.SlaterMarginalsTwoBodyAlgebra

/-! # Actual ordered two-particle Slater marginals

Lieb–Simon (1977) III.11 (60). The spectator contraction and
factorial cancellation are direct proof.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace LiebThirring

/-- Slater-amplitude squared norms are integrable on every fixed two-particle fiber. -/
theorem integrable_slaterAmplitude_norm_sq_insertParticlePair {N q : ℕ}
    (u : Fin N → State 1 q) (i k : Fin N) (hik : i ≠ k) (x y : Position) :
    Integrable (fun Y : OtherPairConfiguration i k =>
      ‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2) := by
  classical
  have hc : Integrable (fun Y : OtherPairConfiguration i k =>
      ((‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2 : ℝ) : ℂ)) := by
    simp_rw [slaterAmplitude_norm_sq_complex]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro σ _
    apply integrable_finsetSum
    intro τ _
    exact (integrable_orbitalContraction_insertParticlePair (u ∘ σ) (u ∘ τ) i k hik x y).const_mul _
  refine hc.norm.congr ?_
  filter_upwards [] with Y
  simp

/-- Exact complex spectator integral of the normalized amplitude. -/
theorem integral_slaterAmplitude_norm_sq_complex_insertParticlePair {N q : ℕ}
    (u : Fin N → State 1 q) (i k : Fin N) (hik : i ≠ k) (x y : Position) :
    (∫ Y : OtherPairConfiguration i k,
      ((‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) *
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
          (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
          ((orbitalContraction (u (σ i)) (u (τ i)) x *
            orbitalContraction (u (σ k)) (u (τ k)) y) *
            ∏ j : {j : Fin N // j ≠ i ∧ j ≠ k}, inner ℂ (u (σ j)) (u (τ j))) := by
  classical
  have ht (σ τ : Equiv.Perm (Fin N)) : Integrable (fun Y : OtherPairConfiguration i k =>
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ j : Fin N, orbitalContraction (u (σ j)) (u (τ j))
          (particlePosition (insertParticlePair i k x y Y) j)) :=
    (integrable_orbitalContraction_insertParticlePair (u ∘ σ) (u ∘ τ) i k hik x y).const_mul _
  simp_rw [slaterAmplitude_norm_sq_complex, Complex.ofReal_inv]
  rw [integral_const_mul,
    integral_finsetSum Finset.univ (fun σ _ => integrable_finsetSum Finset.univ (fun τ _ => ht σ τ))]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_finsetSum Finset.univ (fun τ _ => ht σ τ)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [integral_const_mul]
  congr 1
  exact integral_orbitalContraction_insertParticlePair (u ∘ σ) (u ∘ τ) i k hik x y

/-- Orthonormal spectator contractions reduce a fixed marginal to its direct and exchanged pairings. -/
theorem integral_slaterAmplitude_norm_sq_complex_insertParticlePair_of_orthonormal {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (i k : Fin N) (hik : i ≠ k) (x y : Position) :
    (∫ Y : OtherPairConfiguration i k,
      ((‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) *
        ∑ σ : Equiv.Perm (Fin N),
          (orbitalContraction (u (σ i)) (u (σ i)) x * orbitalContraction (u (σ k)) (u (σ k)) y -
            orbitalContraction (u (σ i)) (u (σ k)) x * orbitalContraction (u (σ k)) (u (σ i)) y) := by
  rw [integral_slaterAmplitude_norm_sq_complex_insertParticlePair u i k hik x y]
  simp_rw [sum_orthonormal_two_body_spectator u hu _ i k hik x y]


/-- The actual ordered-pair marginal, summed over particle labels. -/
theorem sum_integral_slaterAmplitude_pair_norm_sq {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (x y : Position) :
    (∑ i : Fin N, ∑ k : Fin N, if _hik : i = k then 0 else
      ∫ Y : OtherPairConfiguration i k,
        ‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2) =
      slaterOrbitalDensity u x * slaterOrbitalDensity u y - slaterExchangeDensity u x y := by
  classical
  let F : Fin N → Fin N → ℂ := fun j l =>
    orbitalContraction (u j) (u j) x * orbitalContraction (u l) (u l) y -
      orbitalContraction (u j) (u l) x * orbitalContraction (u l) (u j) y
  have hi (i k : Fin N) :
      ((if _hik : i = k then (0 : ℝ) else ∫ Y : OtherPairConfiguration i k,
        ‖slaterAmplitude u (insertParticlePair i k x y Y)‖ ^ 2 : ℝ) : ℂ) =
      ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) *
        ∑ σ : Equiv.Perm (Fin N), if i = k then 0 else F (σ i) (σ k) := by
    by_cases hik : i = k
    · simp [hik]
    · simp only [dite_eq_right hik, ← integral_complex_ofReal, ite_eq_right hik]
      exact integral_slaterAmplitude_norm_sq_complex_insertParticlePair_of_orthonormal
        u hu i k hik x y
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum]
  simp_rw [hi]
  simp_rw [← Finset.mul_sum]
  have hswap : (∑ i : Fin N, ∑ k : Fin N, ∑ σ : Equiv.Perm (Fin N),
      if i = k then (0 : ℂ) else F (σ i) (σ k)) =
      ∑ σ : Equiv.Perm (Fin N), ∑ i : Fin N, ∑ k : Fin N,
        if i = k then 0 else F (σ i) (σ k) := by
    calc
      _ = ∑ i : Fin N, ∑ σ : Equiv.Perm (Fin N), ∑ k : Fin N,
          if i = k then (0 : ℂ) else F (σ i) (σ k) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap, sum_permutation_sum_particle_pair F, ← mul_assoc,
    slater_normalization_factor_mul_factorial, one_mul]
  calc
    _ = ∑ j : Fin N, ∑ l : Fin N, F j l := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      by_cases hjl : j = l
      · subst l; simp [F]
      · simp [hjl]
    _ = _ := sum_orbitalContraction_pair_eq_direct_sub_exchange u x y

/-- Extended ordered-pair marginals equal the literal direct-minus-exchange density. -/
theorem sum_lintegral_slaterAmplitude_pair_norm_sq {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (x y : Position) :
    (∑ i : Fin N, ∑ k : Fin N, if _hik : i = k then 0 else
      ∫⁻ Y : OtherPairConfiguration i k,
        (‖slaterAmplitude u (insertParticlePair i k x y Y)‖₊ : ℝ≥0∞) ^ 2) =
      ENNReal.ofReal (slaterOrbitalDensity u x * slaterOrbitalDensity u y -
        slaterExchangeDensity u x y) := by
  classical
  have hi (i k : Fin N) :
      (if _hik : i = k then (0 : ℝ≥0∞) else ∫⁻ Y : OtherPairConfiguration i k,
        (‖slaterAmplitude u (insertParticlePair i k x y Y)‖₊ : ℝ≥0∞)^2) =
      ENNReal.ofReal (if _hik : i = k then (0 : ℝ) else ∫ Y : OtherPairConfiguration i k,
        ‖slaterAmplitude u (insertParticlePair i k x y Y)‖^2) := by
    by_cases hik : i = k
    · simp [hik]
    · simp only [dite_eq_right hik]
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_slaterAmplitude_norm_sq_insertParticlePair u i k hik x y)
        (Filter.Eventually.of_forall fun Y => sq_nonneg _)]
      apply lintegral_congr
      intro Y
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have hn (i k : Fin N) : 0 ≤ (if _hik : i = k then (0 : ℝ) else
      ∫ Y : OtherPairConfiguration i k,
        ‖slaterAmplitude u (insertParticlePair i k x y Y)‖^2) := by
    split
    · exact le_rfl
    · exact integral_nonneg (fun Y => sq_nonneg _)
  simp_rw [hi, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hn _ k)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hn i k)),
    sum_integral_slaterAmplitude_pair_norm_sq u hu x y]

end LiebThirring
end
