/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormDensityPermutation
import LiebThirring.Sobolev.FormDensitySupport

/-!
# Antisymmetric compact smooth form core

The finite signed permutation average fixes antisymmetric states, preserves
compact smoothness, and is contractive for both mass and the Fourier graph
seminorm. Applying it to the compact smooth form approximation gives the
antisymmetric compact core on the carriers.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.Sobolev

/-- The fermionic sign as a complex scalar. -/
@[expose] def fermionSign {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℂ :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)

/-- The fermionic sign has modulus one. -/
theorem norm_fermionSign {N : ℕ} (σ : Equiv.Perm (Fin N)) : ‖fermionSign σ‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [fermionSign, h]

/-- Fermionic signs multiply according to permutation composition. -/
theorem fermionSign_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    fermionSign (σ * τ) = fermionSign σ * fermionSign τ := by
  simp only [fermionSign, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]

/-- Each fermionic sign is its own inverse. -/
theorem fermionSign_mul_self {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    fermionSign σ * fermionSign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [fermionSign, h]

/-- The signed finite permutation average on the L² state carrier. -/
@[expose] noncomputable def antisymmetrizeStateCLM (N q : ℕ) : State N q →L[ℂ] State N q :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N), fermionSign σ • permutationStateCLM (q := q) σ

/-- The same simultaneous permutation acting on Schwartz functions as a linear map. -/
@[expose] noncomputable def permutationSchwartzCLM {N q : ℕ} (σ : Equiv.Perm (Fin N)) :
    𝓢(Configuration N, SpinAmplitudes N q) →L[ℂ] 𝓢(Configuration N, SpinAmplitudes N q) :=
  (SchwartzMap.postcompCLM
    (spinPermutationLinearIsometryEquiv (q := q) σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (permutationLinearIsometryEquiv σ).toContinuousLinearEquiv)

/-- The signed finite permutation average on Schwartz functions. -/
@[expose] noncomputable def antisymmetrizeSchwartz {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) : 𝓢(Configuration N, SpinAmplitudes N q) :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N), fermionSign σ • permutationSchwartzCLM σ f

/-- The Schwartz signed average represents exactly the state signed average. -/
theorem antisymmetrizeSchwartz_toLp {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (antisymmetrizeSchwartz f).toLp 2 volume = antisymmetrizeStateCLM N q (f.toLp 2 volume) := by
  change (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume)
    ((Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), fermionSign σ • permutationSchwartzCLM σ f) = _
  rw [map_smul, map_sum]
  have hs (σ : Equiv.Perm (Fin N)) : permutationSchwartzCLM σ f =
      permuteSchwartz σ f := rfl
  have hu (σ : Equiv.Perm (Fin N)) (u : State N q) : permutationStateCLM σ u =
      simultaneousPermutation σ u := rfl
  simp only [map_smul, SchwartzMap.toLpCLM_apply, hs, permuteSchwartz_toLp,
    antisymmetrizeStateCLM, smul_apply, sum_apply, hu]

/-- The signed average fixes every state satisfying the antisymmetry predicate. -/
theorem antisymmetrizeStateCLM_eq_self {N q : ℕ} (u : State N q) (hu : antisymmetric u) :
    antisymmetrizeStateCLM N q u = u := by
  have hm : (Fintype.card (Equiv.Perm (Fin N)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hp (σ : Equiv.Perm (Fin N)) : permutationStateCLM σ u =
      simultaneousPermutation σ u := rfl
  simp only [antisymmetrizeStateCLM, smul_apply, sum_apply, hp,
    simultaneousPermutation_eq_sign_smul _ u hu]
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    (∑ σ : Equiv.Perm (Fin N), fermionSign σ • (fermionSign σ • u)) = u
  simp only [smul_smul, fermionSign_mul_self, one_smul, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- Simultaneous permutation composition on Schwartz functions. -/
theorem permuteSchwartz_mul {N q : ℕ} (τ σ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    permuteSchwartz τ (permuteSchwartz σ f) = permuteSchwartz (τ * σ) f := by
  ext x s
  simp only [permuteSchwartz_apply]
  change f (permutePositions σ (permutePositions τ x))
    (permuteSpins σ (permuteSpins τ s)) = f (permutePositions (τ * σ) x) (permuteSpins (τ * σ) s)
  have hx : permutePositions σ (permutePositions τ x) = permutePositions (τ * σ) x := by
    ext a
    rfl
  have hs : permuteSpins σ (permuteSpins τ s) = permuteSpins (τ * σ) s := by
    funext i
    rfl
  rw [hx, hs]

/-- Every Schwartz signed average has the fermionic simultaneous-permutation identity. -/
theorem permuteSchwartz_antisymmetrize {N q : ℕ} (τ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    permuteSchwartz τ (antisymmetrizeSchwartz f) = fermionSign τ • antisymmetrizeSchwartz f := by
  change permutationSchwartzCLM τ (antisymmetrizeSchwartz f) = _
  unfold antisymmetrizeSchwartz
  rw [map_smul, map_sum]
  simp only [map_smul]
  change (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹ •
    (∑ σ : Equiv.Perm (Fin N), fermionSign σ • permuteSchwartz τ (permuteSchwartz σ f)) = _
  simp only [permuteSchwartz_mul]
  rw [smul_comm (fermionSign τ) (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹]
  congr 1
  rw [Finset.smul_sum]
  have heq (σ : Equiv.Perm (Fin N)) : fermionSign σ • permuteSchwartz (τ * σ) f =
      fermionSign τ • (fermionSign (τ * σ) • permuteSchwartz (τ * σ) f) := by
    rw [smul_smul, fermionSign_mul, ← mul_assoc, fermionSign_mul_self, one_mul]
  simp_rw [heq]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => fermionSign τ • (fermionSign σ • permuteSchwartz σ f))

/-- The signed Schwartz average is antisymmetric on the state carrier. -/
theorem antisymmetric_antisymmetrizeSchwartz {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    antisymmetric ((antisymmetrizeSchwartz f).toLp 2 volume) := by
  intro τ
  have heq : simultaneousPermutation τ ((antisymmetrizeSchwartz f).toLp 2 volume) =
      fermionSign τ • (antisymmetrizeSchwartz f).toLp 2 volume := by
    rw [← permuteSchwartz_toLp, permuteSchwartz_antisymmetrize]
    exact (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume).map_smul _ _
  filter_upwards [simultaneousPermutation_apply_ae τ ((antisymmetrizeSchwartz f).toLp 2 volume),
    Lp.coeFn_smul (fermionSign τ) ((antisymmetrizeSchwartz f).toLp 2 volume)] with x hx hs
  intro s
  rw [← hx s, heq, hs]
  rfl

/-- Signed finite permutation averages preserve compact support. -/
theorem antisymmetrizeSchwartz_hasCompactSupport {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (hf : HasCompactSupport f) :
    HasCompactSupport (antisymmetrizeSchwartz f) := by
  unfold antisymmetrizeSchwartz
  refine hasCompactSupport_schwartz_smul
    (Fintype.card (Equiv.Perm (Fin N)) : ℂ)⁻¹
    (∑ σ : Equiv.Perm (Fin N), fermionSign σ • permutationSchwartzCLM σ f) ?_
  refine hasCompactSupport_schwartz_finsetSum Finset.univ
    (fun σ : Equiv.Perm (Fin N) => fermionSign σ • permutationSchwartzCLM σ f) ?_
  intro σ _
  exact hasCompactSupport_schwartz_smul (fermionSign σ) (permuteSchwartz σ f)
    (permuteSchwartz_hasCompactSupport σ f hf)

end LiebThirring.Sobolev

end
