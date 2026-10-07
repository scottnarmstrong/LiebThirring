/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDiagonal
public import LiebThirring.Variational.FormAlgebra
import LiebThirring.Variational.FormIntegralAlgebra

/-! # Sesquilinearity, Hermitian symmetry, and polarization

Form polarization for the energy form. Integrability is supplied by `FormDiagonal`.
-/

public section
open MeasureTheory
open scoped ComplexConjugate ENNReal NNReal
namespace LiebThirring

/-- The energy form is Hermitian, with the first slot conjugated. -/
theorem energyForm_conj_symm {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ : FormDomain N q) :
    conj (energyForm z R hR φ ψ) = energyForm z R hR ψ φ := by
  unfold energyForm
  rw [map_add, map_add, map_mul, Complex.conj_ofReal, inner_conj_symm,
    integral_ofReal_mul_inner_conj, integral_ofReal_mul_inner_conj]

/-- Additivity in the second state. -/
theorem energyForm_add_right {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ χ : FormDomain N q) :
    energyForm z R hR φ (ψ + χ) = energyForm z R hR φ ψ + energyForm z R hR φ χ := by
  unfold energyForm
  rw [formDomain_coe_add, map_add,
    integral_mul_inner_add_right _ _ _ _ (integrable_energyForm_kinetic φ ψ)
      (integrable_energyForm_kinetic φ χ),
    integral_mul_inner_add_right _ _ _ _ (integrable_energyForm_potential z R φ ψ)
      (integrable_energyForm_potential z R φ χ), inner_add_right, mul_add]
  abel

/-- Complex linearity in the second state. -/
theorem energyForm_smul_right {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (c : ℂ) (φ ψ : FormDomain N q) :
    energyForm z R hR φ (c • ψ) = c * energyForm z R hR φ ψ := by
  unfold energyForm
  rw [formDomain_coe_smul, map_smul, integral_mul_inner_smul_right,
    integral_mul_inner_smul_right, inner_smul_right]
  ring

/-- Additivity in the first state. -/
theorem energyForm_add_left {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ χ : FormDomain N q) :
    energyForm z R hR (φ + ψ) χ = energyForm z R hR φ χ + energyForm z R hR ψ χ := by
  rw [← energyForm_conj_symm z R hR χ (φ + ψ), energyForm_add_right, map_add,
    energyForm_conj_symm, energyForm_conj_symm]

/-- Complex conjugate-linearity in the first state. -/
theorem energyForm_smul_left {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (c : ℂ) (φ ψ : FormDomain N q) :
    energyForm z R hR (c • φ) ψ = conj c * energyForm z R hR φ ψ := by
  rw [← energyForm_conj_symm z R hR ψ (c • φ), energyForm_smul_right,
    map_mul, energyForm_conj_symm]

/-- Quadratic homogeneity of the unnormalized real energy. -/
theorem realEnergy_smul {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (c : ℂ) (ψ : FormDomain N q) :
    realEnergy z R hR (c • ψ) = ‖c‖ ^ 2 * realEnergy z R hR ψ := by
  apply Complex.ofReal_injective
  rw [← energyForm_self, energyForm_smul_left, energyForm_smul_right]
  rw [← mul_assoc, Complex.conj_mul']
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [energyForm_self]

/-- Negation in the second state. -/
theorem energyForm_neg_right {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ : FormDomain N q) :
    energyForm z R hR φ (-ψ) = -energyForm z R hR φ ψ := by
  simpa only [neg_one_smul, neg_mul, one_mul] using
    energyForm_smul_right z R hR (-1) φ ψ

/-- Negation in the first state. -/
theorem energyForm_neg_left {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ : FormDomain N q) :
    energyForm z R hR (-φ) ψ = -energyForm z R hR φ ψ := by
  simpa only [neg_one_smul, map_neg, map_one, neg_mul, one_mul] using
    energyForm_smul_left z R hR (-1) φ ψ

end LiebThirring
end
