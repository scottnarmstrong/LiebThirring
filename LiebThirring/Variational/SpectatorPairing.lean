/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorKinetic

/-! # The real atomic cross form for a selected-coordinate multiplier

A multiplier in a single coordinate need not preserve antisymmetry. This module takes the real
part of the literal full-space form.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Variational
open Sobolev

/-- The real potential pairing of a real selected-coordinate multiplier is its literal density. -/
theorem re_integral_potential_selected_multiplier {N q : ℕ} (Z : ℝ≥0)
    (i : Fin N) (u : State N q) (hu : kineticEnergy u < ⊤)
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C b) :
    (∫ X : Configuration N,
      (((electronRepulsion X).toReal -
        (attraction (fun _ : Fin 1 => Z) (fun _ => 0) X).toReal : ℝ) : ℂ) *
      inner ℂ ((lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i))
        B (fun X => hB (particlePosition X i))
        (lipschitzWith_selected_multiplier i b C hb) u) X) (u X)).re =
    ∫ X : Configuration N, b (particlePosition X i) *
      ((electronRepulsion X).toReal -
        (attraction (fun _ : Fin 1 => Z) (fun _ => 0) X).toReal) * ‖u X‖ ^ 2 := by
  let v := lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i))
    B (fun X => hB (particlePosition X i))
    (lipschitzWith_selected_multiplier i b C hb) u
  have hv : kineticEnergy v < ⊤ := kineticEnergy_lipschitzBoundedSMul_lt_top u hu
    _ B _ C (lipschitzWith_selected_multiplier i b C hb)
  have hi := integrable_fullEnergyForm_potential (fun _ : Fin 1 => Z) (fun _ => 0) v u hv hu
  calc
    _ = ∫ X : Configuration N,
        ( (((electronRepulsion X).toReal -
          (attraction (fun _ : Fin 1 => Z) (fun _ => 0) X).toReal : ℝ) : ℂ) *
          inner ℂ (v X) (u X)).re := (integral_re hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [lipschitzBoundedSMul_coeFn
        (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u]
        with X hX
      rw [hX, inner_smul_left, Complex.conj_ofReal]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      have hnorm : (inner ℂ (u X) (u X)).re = ‖u X‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (u X)).symm
      rw [hnorm]
      ring

/-- The atomic cross form minus its energy-weighted mass has a real weak-gradient representation. -/
theorem re_fullEnergyForm_selected_multiplier {N q : ℕ} (Z : ℝ≥0)
    (i : Fin N) (u : State N q) (hu : kineticEnergy u < ⊤)
    (g G : (Fin N × Fin 3) → State N q) (hg : ∀ c, HasWeakDerivative c u (g c))
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C b)
    (hG : ∀ c, HasWeakDerivative c
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u)
      (G c)) (E : ℝ) :
    (fullEnergyForm (fun _ : Fin 1 => Z) (fun _ => 0)
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u) u -
      (E : ℂ) * inner ℂ
        (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
          (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u) u).re =
      (∑ c, inner ℂ (G c) (g c)).re +
      (∫ X : Configuration N, b (particlePosition X i) *
        ((electronRepulsion X).toReal -
          (attraction (fun _ : Fin 1 => Z) (fun _ => 0) X).toReal) * ‖u X‖ ^ 2) -
      E * (inner ℂ
        (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
          (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u) u).re := by
  rw [fullEnergyForm_eq_weakDerivatives _ _ _ _ G g hG hg]
  have hnuc : nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => (0 : Position)) = 0 := by
    simp [nuclearRepulsion]
  rw [hnuc]
  simp only [ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [re_integral_potential_selected_multiplier Z i u hu b B hB C hb]

end LiebThirring.Variational
end
