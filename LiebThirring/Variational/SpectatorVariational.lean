/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialVariational
public import LiebThirring.Ionization.AtomicGroundStateEnergy

/-!
# Variational sign of the atomic spectator form

The unnormalized variational inequality applies separately to every selected-spin residual state.
Summing those inequalities and multiplying by a nonnegative selected-coordinate weight gives the
spectator sign used in the weighted ionization argument.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring.Variational

abbrev atomicPositionInjective : Function.Injective (fun _ : Fin 1 => (0 : Position)) :=
  fun _ _ _ => Subsingleton.elim _ _

theorem atomicGroundStateEnergy_toReal_mul_norm_sq_le_realEnergy (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (u : FormDomain N q) :
    (atomicGroundStateEnergy N q Z).toReal * ‖(u : State N q)‖ ^ 2 ≤
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0) atomicPositionInjective u := by
  exact groundStateEnergy_toReal_mul_norm_sq_le_realEnergy q hq N 1
    (fun _ => Z) (fun _ => 0) atomicPositionInjective u

theorem atomic_spectator_defect_nonneg (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (Z : ℝ≥0)
    (E : ℝ) (hE : E ≤ (atomicGroundStateEnergy N q Z).toReal)
    (u : FormDomain N q) :
    0 ≤ realEnergy (fun _ : Fin 1 => Z) (fun _ => 0) atomicPositionInjective u -
      E * ‖(u : State N q)‖ ^ 2 := by
  have hvar := atomicGroundStateEnergy_toReal_mul_norm_sq_le_realEnergy q hq N Z u
  have hmass := mul_le_mul_of_nonneg_right hE (sq_nonneg ‖(u : State N q)‖)
  linarith only [hvar, hmass]

end LiebThirring.Variational

end
