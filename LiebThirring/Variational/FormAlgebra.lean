/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
public import LiebThirring.Kinetic.Permutation

/-! # Algebra of the antisymmetric form domain

The finite Fourier kinetic domain is stable under addition and scalar multiplication.
These facts give the subtype its natural complex module structure.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- Squared triangle inequality used under nonnegative weighted integrals. -/
theorem enorm_add_sq_le {E : Type*} [NormedAddCommGroup E] (u v : E) :
    (‖u + v‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖u‖₊ : ℝ≥0∞) ^ 2 + (‖v‖₊ : ℝ≥0∞) ^ 2) := by
  have h : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_add_le u v) |>.trans (by nlinarith only [sq_nonneg (‖u‖ - ‖v‖)])
  have he := ENNReal.ofReal_le_ofReal h
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm] using he

/-- Quadratic triangle bound for the extended Fourier kinetic energy. -/
theorem kineticEnergy_add_le {N q : ℕ} (φ ψ : State N q) :
    kineticEnergy (φ + ψ) ≤ 2 * (kineticEnergy φ + kineticEnergy ψ) := by
  let F := Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
  let w : Configuration N → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2
  have hmeas : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  unfold kineticEnergy
  rw [map_add]
  calc
    _ ≤ ∫⁻ ξ : Configuration N,
        2 * (w ξ * (‖(F φ) ξ‖₊ : ℝ≥0∞) ^ 2 +
          w ξ * (‖(F ψ) ξ‖₊ : ℝ≥0∞) ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [Lp.coeFn_add (F φ) (F ψ)] with ξ hξ
      dsimp only [Pi.add_apply] at hξ
      rw [hξ]
      exact (mul_le_mul_right (enorm_add_sq_le ((F φ) ξ) ((F ψ) ξ)) (w ξ)).trans_eq
        (by ring)
    _ = _ := by
      rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left]
      exact hmeas.mul ((Lp.stronglyMeasurable (F φ)).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)

/-- Addition preserves finite Fourier kinetic energy. -/
theorem kineticEnergy_add_lt_top {N q : ℕ} {φ ψ : State N q}
    (hφ : kineticEnergy φ < ⊤) (hψ : kineticEnergy ψ < ⊤) :
    kineticEnergy (φ + ψ) < ⊤ :=
  (kineticEnergy_add_le φ ψ).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hφ, hψ⟩))

/-- Exact unnormalized kinetic homogeneity. -/
theorem kineticEnergy_smul {N q : ℕ} (c : ℂ) (ψ : State N q) :
    kineticEnergy (c • ψ) = (‖c‖₊ : ℝ≥0∞) ^ 2 * kineticEnergy ψ := by
  unfold kineticEnergy
  rw [map_smul]
  calc
    _ = ∫⁻ ξ : Configuration N, (‖c‖₊ : ℝ≥0∞) ^ 2 *
        (ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
          (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_smul c
        (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ)] with ξ hξ
      dsimp only [Pi.smul_apply] at hξ
      rw [hξ, nnnorm_smul, ENNReal.coe_mul, mul_pow]
      ring
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- Scalar multiplication preserves antisymmetry. -/
theorem antisymmetric_smul {N q : ℕ} (c : ℂ) {ψ : State N q}
    (hψ : antisymmetric ψ) : antisymmetric (c • ψ) := by
  intro σ
  have h := Lp.coeFn_smul c ψ
  filter_upwards [hψ σ, h, (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae h]
    with X hψX hX hσX
  intro s
  rw [hσX, hX]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, hψX]
  ring

/-- Addition preserves antisymmetry. -/
theorem antisymmetric_add {N q : ℕ} {φ ψ : State N q}
    (hφ : antisymmetric φ) (hψ : antisymmetric ψ) : antisymmetric (φ + ψ) := by
  intro σ
  have h := Lp.coeFn_add φ ψ
  filter_upwards [hφ σ, hψ σ, h,
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae h] with X hφX hψX hX hσX
  intro s
  rw [hσX, hX]
  simp only [Pi.add_apply, PiLp.add_apply, hφX, hψX, mul_add]

/-- Zero belongs to the form domain. -/
theorem formDomain_zero_mem {N q : ℕ} :
    antisymmetric (0 : State N q) ∧ kineticEnergy (0 : State N q) < ⊤ := by
  have hz : antisymmetric (0 : State N q) := by
    intro σ
    have h := Lp.coeFn_zero (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))
    filter_upwards [h, (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae h]
      with X hX hσX
    intro s
    rw [hσX, hX]
    simp only [Pi.zero_apply, PiLp.zero_apply, mul_zero]
  refine ⟨hz, ?_⟩
  have hk := kineticEnergy_smul (0 : ℂ) (0 : State N q)
  have he : kineticEnergy (0 : State N q) = 0 := by
    simpa only [zero_smul, nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_mul] using hk
  rw [he]
  exact ENNReal.zero_lt_top

/-- The form domain is a complex submodule of the original L² state space. -/
@[expose] noncomputable def formDomainSubmodule (N q : ℕ) : Submodule ℂ (State N q) where
  carrier := {ψ | antisymmetric ψ ∧ kineticEnergy ψ < ⊤}
  zero_mem' := formDomain_zero_mem
  add_mem' hφ hψ := ⟨antisymmetric_add hφ.1 hψ.1, kineticEnergy_add_lt_top hφ.2 hψ.2⟩
  smul_mem' c ψ hψ := ⟨antisymmetric_smul c hψ.1, by
    rw [kineticEnergy_smul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hψ.2⟩

noncomputable instance {N q : ℕ} : AddCommGroup (FormDomain N q) :=
  inferInstanceAs (AddCommGroup (formDomainSubmodule N q))

noncomputable instance {N q : ℕ} : Module ℂ (FormDomain N q) :=
  inferInstanceAs (Module ℂ (formDomainSubmodule N q))

@[simp] theorem formDomain_coe_add {N q : ℕ} (φ ψ : FormDomain N q) :
    ((φ + ψ : FormDomain N q) : State N q) = (φ : State N q) + (ψ : State N q) := rfl

@[simp] theorem formDomain_coe_smul {N q : ℕ} (c : ℂ) (ψ : FormDomain N q) :
    ((c • ψ : FormDomain N q) : State N q) = c • (ψ : State N q) := rfl

@[simp] theorem formDomain_coe_zero {N q : ℕ} :
    ((0 : FormDomain N q) : State N q) = 0 := rfl

end LiebThirring
end
