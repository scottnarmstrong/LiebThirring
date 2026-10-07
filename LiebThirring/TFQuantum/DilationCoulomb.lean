/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationState
public import LiebThirring.Defs.Coulomb
/-! # Coulomb dilation on electronic states

Coulomb expectations and nuclear energy scale exactly under normalized spatial dilation.
All identities hold on the whole state carrier in extended nonnegative form.
direct proof calculation.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Dilation

theorem coulombKernel_smul (r : ℝ) (hr : 0 < r) (x y : Position) :
    coulombKernel (r • x) (r • y) = (ENNReal.ofReal r)⁻¹ * coulombKernel x y := by
  unfold coulombKernel
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    ENNReal.ofReal_mul hr.le,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hr).ne') (Or.inl ENNReal.ofReal_ne_top)]

theorem coulombKernel_inv_smul (r : ℝ) (hr : 0 < r) (x y : Position) :
    coulombKernel (r⁻¹ • x) (r⁻¹ • y) = ENNReal.ofReal r * coulombKernel x y := by
  rw [coulombKernel_smul r⁻¹ (inv_pos.mpr hr), ENNReal.ofReal_inv_of_pos hr, inv_inv]

theorem electronRepulsion_inv_smul {N : ℕ} (r : ℝ) (hr : 0 < r) (x : Configuration N) :
    electronRepulsion (r⁻¹ • x) = ENNReal.ofReal r * electronRepulsion x := by
  simp only [electronRepulsion, particlePosition_smul, coulombKernel_inv_smul r hr,
    Finset.mul_sum]

theorem attraction_inv_smul {N M : ℕ} (r : ℝ) (hr : 0 < r)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction z (fun k => r⁻¹ • R k) (r⁻¹ • x) = ENNReal.ofReal r * attraction z R x := by
  simp only [attraction, particlePosition_smul, coulombKernel_inv_smul r hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem attraction_charge_smul {N M : ℕ} (β : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction (fun k => β * z k) R x = (β : ℝ≥0∞) * attraction z R x := by
  simp only [attraction, ENNReal.coe_mul, Finset.mul_sum, mul_assoc]

theorem nuclearRepulsion_dilation {M : ℕ} (r : ℝ) (hr : 0 < r) (β : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    nuclearRepulsion (fun k => β * z k) (fun k => r⁻¹ • R k) =
      (β : ℝ≥0∞)^2 * ENNReal.ofReal r * nuclearRepulsion z R := by
  simp only [nuclearRepulsion, ENNReal.coe_mul, coulombKernel_inv_smul r hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Dilation

theorem repulsion_stateDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r) (ψ : State N q) :
    (∫⁻ x : Configuration N, electronRepulsion x *
      (‖stateDilationEquiv r hr ψ x‖₊ : ℝ≥0∞)^2) =
    ENNReal.ofReal r * ∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞)^2 := by
  rw [lintegral_weight_stateDilationEquiv]
  simp_rw [Dilation.electronRepulsion_inv_smul r hr, mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem attraction_stateDilationEquiv {N q M : ℕ} (r : ℝ) (hr : 0 < r) (β : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q) :
    (∫⁻ x : Configuration N, attraction (fun k => β * z k) (fun k => r⁻¹ • R k) x *
      (‖stateDilationEquiv r hr ψ x‖₊ : ℝ≥0∞)^2) =
    ((β : ℝ≥0∞) * ENNReal.ofReal r) *
      ∫⁻ x : Configuration N, attraction z R x * (‖ψ x‖₊ : ℝ≥0∞)^2 := by
  rw [lintegral_weight_stateDilationEquiv]
  simp_rw [Dilation.attraction_charge_smul, Dilation.attraction_inv_smul r hr]
  calc
    _ = ∫⁻ x, ((β : ℝ≥0∞) * ENNReal.ofReal r) *
        (attraction z R x * (‖ψ x‖₊ : ℝ≥0∞)^2) := by
      apply lintegral_congr
      intro x
      ring
    _ = _ := lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
end LiebThirring
end
