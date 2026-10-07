/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormDensityAntisymmetric

/-!
# Antisymmetric compact smooth density

The signed permutation average contracts both the L² norm and the kinetic
form. Compact smooth approximants can therefore be chosen antisymmetric.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.Sobolev

/-- Explicit finite-sum formula for the signed state average. -/
theorem antisymmetrizeStateCLM_apply_sum {N q : ℕ} (u : State N q) :
    antisymmetrizeStateCLM N q u = (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), fermionSign σ • simultaneousPermutation σ u := by
  have hp (σ : Equiv.Perm (Fin N)) : permutationStateCLM σ u =
      simultaneousPermutation σ u := rfl
  simp only [antisymmetrizeStateCLM, smul_apply, sum_apply, hp]

/-- The signed state average contracts the L² norm. -/
theorem norm_antisymmetrizeStateCLM_le {N q : ℕ} (u : State N q) :
    ‖antisymmetrizeStateCLM N q u‖ ≤ ‖u‖ := by
  let m : ℕ := Fintype.card (Equiv.Perm (Fin N))
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hnorm : ‖(m : ℂ)⁻¹‖ = (m : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  rw [antisymmetrizeStateCLM_apply_sum, norm_smul]
  change ‖(m : ℂ)⁻¹‖ * ‖∑ σ : Equiv.Perm (Fin N), fermionSign σ • simultaneousPermutation σ u‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), ‖fermionSign σ • simultaneousPermutation σ u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = (m : ℝ)⁻¹ * ((m : ℝ) * ‖u‖) := by
      simp only [norm_smul, norm_fermionSign, norm_simultaneousPermutation, one_mul,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    _ = ‖u‖ := by rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- The signed state average contracts the radial Fourier graph seminorm. -/
theorem fourierGraphSeminorm_antisymmetrizeStateCLM_le {N q : ℕ} (u : State N q) :
    fourierGraphSeminorm (antisymmetrizeStateCLM N q u) ≤ fourierGraphSeminorm u := by
  let m : ℕ := Fintype.card (Equiv.Perm (Fin N))
  have hm : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hnorm : ‖(m : ℂ)⁻¹‖ = (m : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  have hcoef : ENNReal.ofReal (‖(m : ℂ)⁻¹‖) = (m : ℝ≥0∞)⁻¹ := by
    rw [hnorm, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr Fintype.card_pos)]
    simp only [ENNReal.ofReal_natCast]
    rfl
  rw [antisymmetrizeStateCLM_apply_sum, fourierGraphSeminorm_smul]
  change ENNReal.ofReal ‖(m : ℂ)⁻¹‖ *
    fourierGraphSeminorm (∑ σ : Equiv.Perm (Fin N), fermionSign σ • simultaneousPermutation σ u) ≤ _
  rw [hcoef]
  calc
    _ ≤ (m : ℝ≥0∞)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
        fourierGraphSeminorm (fermionSign σ • simultaneousPermutation σ u) :=
      mul_le_mul' le_rfl (fourierGraphSeminorm_sum_le Finset.univ _)
    _ = (m : ℝ≥0∞)⁻¹ * ((m : ℝ≥0∞) * fourierGraphSeminorm u) := by
      simp only [fourierGraphSeminorm_smul, norm_fermionSign, ENNReal.ofReal_one,
        fourierGraphSeminorm_simultaneousPermutation, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rfl
    _ = fourierGraphSeminorm u := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hm (ENNReal.natCast_ne_top m), one_mul]

/-- The signed state average contracts the kinetic form, including infinite energy. -/
theorem kineticEnergy_antisymmetrizeStateCLM_le {N q : ℕ} (u : State N q) :
    kineticEnergy (antisymmetrizeStateCLM N q u) ≤ kineticEnergy u := by
  rw [kineticEnergy_eq_radialFourier_eLpNorm, kineticEnergy_eq_radialFourier_eLpNorm]
  exact mul_le_mul' le_rfl (pow_le_pow_left'
    (fourierGraphSeminorm_antisymmetrizeStateCLM_le u) 2)

/-- Compact smooth antisymmetric states form a core for the kinetic form on every
finite-energy antisymmetric state of the carrier. -/
theorem exists_antisymmetric_compact_smooth_form_approximation {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) (hanti : antisymmetric u) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(Configuration N, SpinAmplitudes N q), HasCompactSupport f ∧
      antisymmetric (f.toLp 2 volume) ∧ ‖u - f.toLp 2 volume‖ ≤ ε ∧
      kineticEnergy (u - f.toLp 2 volume) ≤ ENNReal.ofReal ((2 * Real.pi * ε) ^ 2) := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_compact_smooth_form_approximation u hu hε
  have heq : u - (antisymmetrizeSchwartz f).toLp 2 volume =
      antisymmetrizeStateCLM N q (u - f.toLp 2 volume) := by
    rw [map_sub, antisymmetrizeStateCLM_eq_self u hanti, antisymmetrizeSchwartz_toLp]
  refine ⟨antisymmetrizeSchwartz f, antisymmetrizeSchwartz_hasCompactSupport f hf,
    antisymmetric_antisymmetrizeSchwartz f, ?_, ?_⟩
  · rw [heq]
    exact (norm_antisymmetrizeStateCLM_le _).trans h₀
  · rw [heq]
    exact (kineticEnergy_antisymmetrizeStateCLM_le _).trans h₁

end LiebThirring.Sobolev

end
