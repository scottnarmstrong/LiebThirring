/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteOrbitals

/-! # Uniform eventual kinetic estimates for the remote family

The kinetic cost tends to zero uniformly in translation. A scalar tolerance
also controls the eventual sum of kinetic and Coulomb costs. Translation
is chosen subsequently to separate the main trial support.
direct proof.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap Topology
namespace LiebThirring.TFUpper

/-- A scalar tolerance sufficient for two nonnegative weighted costs. -/
theorem weighted_small_cost_le (A B ε k p : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hk : k ≤ ε / (2 * (A + B + 1)))
    (hp : p ≤ ε / (2 * (A + B + 1))) : A * k + B * p < ε := by
  have hden : 0 < 2 * (A + B + 1) := by linarith only [hA, hB]
  have hδ : 0 < ε / (2 * (A + B + 1)) := div_pos hε hden
  calc
    A * k + B * p ≤ (A + B) * (ε / (2 * (A + B + 1))) := by
      calc
        _ ≤ A * (ε / (2 * (A + B + 1))) + B * (ε / (2 * (A + B + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left hk hA) (mul_le_mul_of_nonneg_left hp hB)
        _ = _ := (add_mul _ _ _).symm
    _ < (A + B + 1) * (ε / (2 * (A + B + 1))) :=
      mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

theorem eventually_remoteSpinOrbital_kinetic_lt {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ hL : 0 < L, ∀ a : Position,
      (∑ i : Fin r, ∑ k : Fin 3, ∫ x : Position,
        ‖fderiv ℝ (fun y => remoteSpinOrbital h hh t a L hL i y) x
          (PiLp.single 2 k (1 : ℝ))‖ ^ 2) < ε := by
  let K := ∑ k : Fin 3, ∫ x : Position,
    ‖fderiv ℝ (fun y => h y) x (PiLp.single 2 k (1 : ℝ))‖ ^ 2
  have ht : Tendsto (fun L : ℝ => (r : ℝ) * (L⁻¹ ^ 2 * K)) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero] using
      ((tendsto_inv_atTop_zero.pow 2).mul_const K).const_mul (r : ℝ)
  filter_upwards [ht.eventually_lt_const hε] with L hsmall hL a
  rw [sum_remoteSpinOrbital_kinetic]
  exact hsmall

end LiebThirring.TFUpper
end
