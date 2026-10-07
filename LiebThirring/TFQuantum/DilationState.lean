/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationBasic
public import LiebThirring.Variational.FormDomain
public import LiebThirring.Kinetic.Permutation
/-! # Dilation on the electronic state carrier

The exact normalized spatial dilation preserves the simultaneous spin and
space antisymmetry, and its reciprocal scale is its inverse.
direct proof calculation.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring

@[expose] noncomputable def stateDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r) :
    State N q ≃ₗᵢ[ℂ] State N q := Dilation.linearIsometryEquiv r hr

@[simp] theorem stateDilationEquiv_norm {N q : ℕ} (r : ℝ) (hr : 0 < r) (ψ : State N q) :
    ‖stateDilationEquiv r hr ψ‖ = ‖ψ‖ := (stateDilationEquiv r hr).norm_map ψ

theorem stateDilationEquiv_apply_ae {N q : ℕ} (r : ℝ) (hr : 0 < r) (ψ : State N q) :
    stateDilationEquiv r hr ψ =ᵐ[volume] fun x =>
      (Dilation.amplitude (Configuration N) r : ℂ) • ψ (r • x) :=
  Dilation.coeFn_applyL2 r hr ψ

@[simp] theorem stateDilationEquiv_inv_apply {N q : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : State N q) : stateDilationEquiv r⁻¹ (inv_pos.mpr hr)
      (stateDilationEquiv r hr ψ) = ψ := Dilation.applyL2_inv_applyL2 r hr ψ

@[simp] theorem stateDilationEquiv_apply_inv {N q : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : State N q) : stateDilationEquiv r hr
      (stateDilationEquiv r⁻¹ (inv_pos.mpr hr) ψ) = ψ := by
  change Dilation.applyL2 r hr (Dilation.applyL2 r⁻¹ (inv_pos.mpr hr) ψ) = ψ
  simpa only [inv_inv] using Dilation.applyL2_inv_applyL2 r⁻¹ (inv_pos.mpr hr) ψ

namespace Dilation

theorem particlePosition_smul {N : ℕ} (r : ℝ) (x : Configuration N) (i : Fin N) :
    particlePosition (r • x) i = r • particlePosition x i := by
  ext a
  rfl

theorem permutePositions_smul {N : ℕ} (r : ℝ) (x : Configuration N)
    (σ : Equiv.Perm (Fin N)) : permutePositions σ (r • x) = r • permutePositions σ x := by
  ext a
  rfl

end Dilation

theorem antisymmetric_stateDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : State N q) (hψ : antisymmetric ψ) : antisymmetric (stateDilationEquiv r hr ψ) := by
  intro σ
  filter_upwards [(Measure.quasiMeasurePreserving_smul volume hr.ne').ae (hψ σ),
    stateDilationEquiv_apply_ae r hr ψ,
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae
      (stateDilationEquiv_apply_ae r hr ψ)] with x hx hu hσ
  intro s
  rw [hu, hσ]
  change (Dilation.amplitude (Configuration N) r : ℂ) *
      ψ (r • permutePositions σ x) (permuteSpins σ s) =
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) *
      ((Dilation.amplitude (Configuration N) r : ℂ) * ψ (r • x) s)
  rw [← Dilation.permutePositions_smul, hx]
  ring

theorem lintegral_weight_stateDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : State N q) (w : Configuration N → ℝ≥0∞) :
    (∫⁻ x, w x * (‖stateDilationEquiv r hr ψ x‖₊ : ℝ≥0∞)^2) =
      ∫⁻ x, w (r⁻¹ • x) * (‖ψ x‖₊ : ℝ≥0∞)^2 :=
  Dilation.lintegral_weight_applyL2 r hr ψ w

end LiebThirring
end
