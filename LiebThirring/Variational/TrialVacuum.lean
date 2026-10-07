/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialConstruction
public import LiebThirring.Ionization.AtomicGroundStateEnergy

/-! # Vacuum variational energy (the normalized trial construction) -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Every vacuum state has zero kinetic energy. -/
theorem kineticEnergy_vacuum {q : ℕ} (u : State 0 q) : kineticEnergy u = 0 := by
  unfold kineticEnergy
  have hz (ξ : Configuration 0) : ξ = 0 := Subsingleton.elim _ _
  calc
    _ = ∫⁻ _ : Configuration 0, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro ξ
      rw [hz ξ]
      simp only [nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, zero_mul]
    _ = 0 := lintegral_zero

/-- The vacuum quadratic form consists exactly of nuclear repulsion times mass. -/
theorem realEnergy_vacuum {q M : ℕ} (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) (u : FormDomain 0 q) :
    realEnergy z R hR u = (nuclearRepulsion z R).toReal * ‖(u : State 0 q)‖ ^ 2 := by
  simp only [realEnergy, kineticEnergy_vacuum, electronRepulsion, attraction,
    Finset.univ_eq_empty, Finset.sum_empty, zero_mul, lintegral_zero,
    ENNReal.toReal_zero, zero_add, sub_zero]

/-- The vacuum infimum is the fixed nuclear repulsion. -/
theorem groundStateEnergy_vacuum (q : ℕ) (hq : 1 ≤ q)
    (M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    groundStateEnergy 0 q M z R hR = ((nuclearRepulsion z R).toReal : EReal) := by
  obtain ⟨u, hu⟩ := exists_normalized_formDomain_trial q hq 0
  let : Nonempty {ψ : FormDomain 0 q // ‖(ψ : State 0 q)‖ = 1} := ⟨⟨u, hu⟩⟩
  have heq (ψ : {ψ : FormDomain 0 q // ‖(ψ : State 0 q)‖ = 1}) :
      realEnergy z R hR ψ.val = (nuclearRepulsion z R).toReal := by
    rw [realEnergy_vacuum, ψ.property, one_pow, mul_one]
  simp only [groundStateEnergy, heq, ciInf_const]

/-- A single nucleus has no nuclear pair repulsion. -/
theorem nuclearRepulsion_single (Z : ℝ≥0) (r : Position) :
    nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => r) = 0 := by
  simp [nuclearRepulsion]

/-- The atomic vacuum energy is zero. -/
theorem atomicGroundStateEnergy_vacuum (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    atomicGroundStateEnergy 0 q Z = 0 := by
  calc
    atomicGroundStateEnergy 0 q Z =
        ((nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => (0 : Position))).toReal : EReal) :=
      groundStateEnergy_vacuum q hq 1 (fun _ => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _)
    _ = 0 := by
      rw [nuclearRepulsion_single, ENNReal.toReal_zero, EReal.coe_zero]

end LiebThirring

end
