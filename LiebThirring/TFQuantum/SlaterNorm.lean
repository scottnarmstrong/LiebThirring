/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterMarginalsExpansion
public import LiebThirring.TFQuantum.SlaterOneBodyAlgebra

/-! # The general spatial-spin Slater state and its norm -/

public section
open MeasureTheory WithLp
open scoped ComplexConjugate
namespace LiebThirring

private theorem continuous_oneParticleConfiguration_norm :
    Continuous oneParticleConfiguration := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 × Fin 3 => ℝ)).comp
    (continuous_pi fun ia => PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ia.2)

private theorem continuous_particlePosition_norm {N : ℕ} (i : Fin N) :
    Continuous (fun x : Configuration N => particlePosition x i) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun a => PiLp.continuous_apply 2
      (fun _ : Fin N × Fin 3 => ℝ) (i, a))

private theorem measurable_orbitalValue_particle {N q : ℕ} (u : State 1 q)
    (i : Fin N) (s : Fin q) :
    Measurable (fun x : Configuration N => orbitalValue u (particlePosition x i) s) := by
  exact (PiLp.continuous_apply 2 (fun _ : SpinLabels 1 q => ℂ)
    (oneParticleSpinLabel s)).measurable.comp
      ((Lp.stronglyMeasurable u).measurable.comp
        (continuous_oneParticleConfiguration_norm.measurable.comp
          (continuous_particlePosition_norm i).measurable))

theorem measurable_slaterDeterminant {N q : ℕ} (u : Fin N → State 1 q)
    (s : SpinLabels N q) : Measurable (fun x => slaterDeterminant u x s) := by
  classical
  simp_rw [slaterDeterminant_eq_sum]
  exact Finset.measurable_sum _ fun σ _ => measurable_const.mul <|
    Finset.measurable_prod _ fun i _ => measurable_orbitalValue_particle (u (σ i)) i (s i)

theorem measurable_slaterAmplitude {N q : ℕ} (u : Fin N → State 1 q) :
    Measurable (slaterAmplitude u) := by
  apply (PiLp.continuous_toLp 2 (fun _ : SpinLabels N q => ℂ)).measurable.comp
  rw [measurable_pi_iff]
  intro s
  exact measurable_const.mul (measurable_slaterDeterminant u s)

theorem slaterAmplitude_norm_sq_complex {N q : ℕ} (u : Fin N → State 1 q)
    (x : Configuration N) :
    ((‖slaterAmplitude u x‖ ^ 2 : ℝ) : ℂ) =
      ((((Real.sqrt N.factorial)⁻¹ : ℝ) : ℂ) ^ 2) *
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ i : Fin N, orbitalContraction (u (σ i)) (u (τ i)) (particlePosition x i) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [slaterAmplitude, PiLp.toLp_apply, Complex.sq_norm, Complex.ofReal_sum]
  have hs (z : ℂ) :
      ((Complex.normSq ((((Real.sqrt N.factorial)⁻¹ : ℝ) : ℂ) * z) : ℝ) : ℂ) =
        ((((Real.sqrt N.factorial)⁻¹ : ℝ) : ℂ) ^ 2) * (conj z * z) := by
    rw [Complex.normSq_mul]
    push_cast
    have hc (c : ℝ) : ((Complex.normSq ((c : ℂ)⁻¹) : ℝ) : ℂ) = ((c : ℂ)⁻¹) ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    have hz : ((Complex.normSq z : ℝ) : ℂ) = conj z * z := by
      apply Complex.ext
      · simp [Complex.normSq_apply, Complex.mul_re]
      · simp [Complex.mul_im]
        ring
    rw [hc, hz]
  simp_rw [hs]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Complex.star_def] using sum_slaterDeterminant_conj_mul u u x

theorem memLp_slaterAmplitude {N q : ℕ} (u : Fin N → State 1 q) :
    MemLp (slaterAmplitude u) 2 volume := by
  classical
  have hsum : Integrable (fun x : Configuration N ↦
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ i : Fin N, orbitalContraction (u (σ i)) (u (τ i)) (particlePosition x i)) := by
    apply integrable_finsetSum Finset.univ
    intro σ _
    apply integrable_finsetSum Finset.univ
    intro τ _
    exact (integrable_prod_orbitalContraction
      (fun i ↦ u (σ i)) (fun i ↦ u (τ i))).const_mul _
  have hc : Integrable (fun x : Configuration N ↦ ((‖slaterAmplitude u x‖ ^ 2 : ℝ) : ℂ)) := by
    refine (hsum.const_mul
      ((((Real.sqrt N.factorial)⁻¹ : ℝ) : ℂ) ^ 2)).congr ?_
    filter_upwards [] with x
    exact (slaterAmplitude_norm_sq_complex u x).symm
  have hr : Integrable (fun x : Configuration N ↦ ‖slaterAmplitude u x‖ ^ 2) := by
    refine hc.norm.congr ?_
    filter_upwards [] with x
    simp
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_slaterAmplitude u).aestronglyMeasurable).2 hr

/-- The normalized determinant as an `N`-particle state. -/
@[expose] noncomputable def slaterState {N q : ℕ} (u : Fin N → State 1 q) : State N q :=
  (memLp_slaterAmplitude u).toLp (slaterAmplitude u)

theorem coeFn_slaterState {N q : ℕ} (u : Fin N → State 1 q) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)), slaterState u x = slaterAmplitude u x :=
  MemLp.coeFn_toLp _

theorem antisymmetric_slaterState {N q : ℕ} (u : Fin N → State 1 q) :
    antisymmetric (slaterState u) := by
  intro σ
  have h := coeFn_slaterState u
  filter_upwards [h,
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae h] with x hx hσx
  intro s
  rw [hσx, hx, slaterAmplitude_permute]

theorem integral_slaterAmplitude_norm_sq_complex_of_orthonormal {N q : ℕ}
    (u : Fin N → State 1 q) (hu : Orthonormal ℂ u) :
    (∫ x : Configuration N, ((‖slaterAmplitude u x‖ ^ 2 : ℝ) : ℂ)) = 1 := by
  classical
  have hterm (σ τ : Equiv.Perm (Fin N)) : Integrable (fun x : Configuration N ↦
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
      ∏ i : Fin N, orbitalContraction (u (σ i)) (u (τ i)) (particlePosition x i)) :=
    (integrable_prod_orbitalContraction
      (fun i ↦ u (σ i)) (fun i ↦ u (τ i))).const_mul _
  rw [integral_congr_ae (ae_of_all _ (slaterAmplitude_norm_sq_complex u))]
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun σ _ ↦
    integrable_finsetSum Finset.univ (fun τ _ ↦ hterm σ τ))]
  simp_rw [integral_finsetSum Finset.univ (fun τ _ ↦ hterm _ τ)]
  simp_rw [integral_const_mul, integral_prod_orbitalContraction]
  have hinner := orthonormal_iff_ite.mp hu
  simp_rw [hinner]
  rw [sum_permutation_delta_products]
  simpa only [Complex.ofReal_inv] using slater_normalization_factor_mul_factorial N

theorem norm_slaterState_of_orthonormal {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) : ‖slaterState u‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  have hrep := coeFn_slaterState u
  have hint : (∫ x : Configuration N, inner ℂ (slaterState u x) (slaterState u x)) = 1 := by
    rw [integral_congr_ae]
    · exact integral_slaterAmplitude_norm_sq_complex_of_orthonormal u hu
    · filter_upwards [hrep] with x hx
      rw [hx]
      simp only [inner_self_eq_norm_sq_to_K]
      norm_cast
  rw [hint]
  norm_num

end LiebThirring
end
