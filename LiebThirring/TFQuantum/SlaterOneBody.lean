/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterNorm
public import LiebThirring.TFQuantum.SlaterMarginalsWeighted
public import LiebThirring.TFQuantum.SlaterDensityRepresentatives

/-! # The actual one-particle Slater density

All spectator integrations are performed on the configuration spaces.
Complex determinant contractions are integrable for every fixed open position.
Summing particle labels cancels the factorial and yields the actual occupied
orbital density, including the vacuum. Proof: Slater determinant identities; Lieb–Simon (1977) III.11 (60),
p. 66; direct proof product integration and normalization calculation.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace LiebThirring

/-- Slater-amplitude squared norms are integrable on every fixed one-particle fiber. -/
theorem integrable_slaterAmplitude_norm_sq_insertParticle {N q : ℕ}
    (u : Fin N → State 1 q) (i : Fin N) (x : Position) :
    Integrable (fun Y : OtherConfiguration i =>
      ‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2) := by
  classical
  have hc : Integrable (fun Y : OtherConfiguration i =>
      ((‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2 : ℝ) : ℂ)) := by
    simp_rw [slaterAmplitude_norm_sq_complex]
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro σ _
    apply integrable_finsetSum
    intro τ _
    exact (integrable_orbitalContraction_insertParticle (u ∘ σ) (u ∘ τ) i x).const_mul _
  refine hc.norm.congr ?_
  filter_upwards [] with Y
  simp

/-- Exact complex spectator integral of the normalized amplitude. -/
theorem integral_slaterAmplitude_norm_sq_complex_insertParticle {N q : ℕ}
    (u : Fin N → State 1 q) (i : Fin N) (x : Position) :
    (∫ Y : OtherConfiguration i,
      ((‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) *
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
          (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
          (orbitalContraction (u (σ i)) (u (τ i)) x *
            ∏ j : {j : Fin N // j ≠ i}, inner ℂ (u (σ j)) (u (τ j))) := by
  classical
  have ht (σ τ : Equiv.Perm (Fin N)) : Integrable (fun Y : OtherConfiguration i =>
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ j : Fin N, orbitalContraction (u (σ j)) (u (τ j))
          (particlePosition (insertParticle i x Y) j)) :=
    (integrable_orbitalContraction_insertParticle (u ∘ σ) (u ∘ τ) i x).const_mul _
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
  exact integral_orbitalContraction_insertParticle (u ∘ σ) (u ∘ τ) i x

/-- Orthonormal spectator contractions reduce a fixed marginal to its diagonal pairings. -/
theorem integral_slaterAmplitude_norm_sq_complex_insertParticle_of_orthonormal {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (i : Fin N) (x : Position) :
    (∫ Y : OtherConfiguration i,
      ((‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) *
        ∑ σ : Equiv.Perm (Fin N), orbitalContraction (u (σ i)) (u (σ i)) x := by
  rw [integral_slaterAmplitude_norm_sq_complex_insertParticle]
  simp_rw [sum_orthonormal_one_body_spectator u hu]

/-- The complete one-particle number density of the amplitude is the occupied orbital trace. -/
theorem sum_integral_slaterAmplitude_norm_sq {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (x : Position) :
    (∑ i : Fin N, ∫ Y : OtherConfiguration i,
      ‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2) = slaterOrbitalDensity u x := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, ← integral_complex_ofReal]
  simp_rw [integral_slaterAmplitude_norm_sq_complex_insertParticle_of_orthonormal u hu]
  rw [← Finset.mul_sum, Finset.sum_comm,
    sum_permutation_sum_particle (fun j => orbitalContraction (u j) (u j) x),
    ← mul_assoc, slater_normalization_factor_mul_factorial, one_mul,
    sum_orbitalContraction_self_eq_density]

/-- Extended one-particle marginals have the same exact occupied-orbital density. -/
theorem sum_lintegral_slaterAmplitude_norm_sq {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (x : Position) :
    (∑ i : Fin N, ∫⁻ Y : OtherConfiguration i,
      (‖slaterAmplitude u (insertParticle i x Y)‖₊ : ℝ≥0∞) ^ 2) =
      ENNReal.ofReal (slaterOrbitalDensity u x) := by
  classical
  have hi (i : Fin N) :
      (∫⁻ Y : OtherConfiguration i,
        (‖slaterAmplitude u (insertParticle i x Y)‖₊ : ℝ≥0∞) ^ 2) =
      ENNReal.ofReal (∫ Y : OtherConfiguration i,
        ‖slaterAmplitude u (insertParticle i x Y)‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_slaterAmplitude_norm_sq_insertParticle u i x)
      (Filter.Eventually.of_forall fun Y => sq_nonneg _)]
    apply lintegral_congr
    intro Y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  simp_rw [hi]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun Y => sq_nonneg _)),
    sum_integral_slaterAmplitude_norm_sq u hu x]

/-- A state represented by the Slater amplitude has exactly the Slater density. -/
theorem density_eq_slaterOrbitalDensity_of_ae_eq {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) (ψ : State N q)
    (hψ : ψ =ᵐ[volume] slaterAmplitude u) :
    density ψ =ᵐ[volume] fun x => ENNReal.ofReal (slaterOrbitalDensity u x) := by
  filter_upwards [density_eq_marginals_of_ae_eq ψ (slaterAmplitude u) hψ] with x hx
  exact hx.trans (sum_lintegral_slaterAmplitude_norm_sq u hu x)

/-- The genuine Slater state's density is precisely the occupied orbital density. -/
theorem density_slaterState {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) :
    density (slaterState u) =ᵐ[volume] fun x => ENNReal.ofReal (slaterOrbitalDensity u x) :=
  density_eq_slaterOrbitalDensity_of_ae_eq u hu (slaterState u) (coeFn_slaterState u)

/-- Every nonnegative density observable tests the actual occupied Slater density. -/
theorem density_slaterState_testing {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (w : Position → ℝ≥0∞) :
    (∫⁻ x : Position, w x * density (slaterState u) x) =
      ∫⁻ x : Position, w x * ENNReal.ofReal (slaterOrbitalDensity u x) := by
  apply lintegral_congr_ae
  filter_upwards [density_slaterState u hu] with x hx
  rw [hx]

end LiebThirring
end
