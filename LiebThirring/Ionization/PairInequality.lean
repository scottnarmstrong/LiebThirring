/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.PairInequalitySelected
public import LiebThirring.Ionization.PairInequalityDensity

/-! # The cutoff pair inequality from the admissible weak sum test -/

public section
open MeasureTheory
open scoped NNReal
namespace LiebThirring

/-- The cutoff pair inequality, with no spatial moment or strict-binding assumption. -/
theorem ionization_cutoff_pair_sum_le {N q : ℕ} (Z : ℝ≥0) (E : ℝ)
    (u : FormDomain (N + 1) q) (hu : ‖(u : State (N + 1) q)‖ = 1)
    (heq : ∀ v : FormDomain (N + 1) q,
      energyForm (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) v u =
        (E : ℂ) * inner ℂ (v : State (N + 1) q) (u : State (N + 1) q))
    (hE : E ≤ (atomicGroundStateEnergy N q Z).toReal) (ε : ℝ) (hε : 0 < ε) :
    (∑ i : Fin (N + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ∫ X : Configuration (N + 1),
        ((ionizationWeight ε ‖particlePosition X i‖ +
          ionizationWeight ε ‖particlePosition X j‖) /
            ‖particlePosition X i - particlePosition X j‖) *
              ‖(u : State (N + 1) q) X‖ ^ 2) ≤ ((N + 1 : ℕ) : ℝ) * Z := by
  have hb (i : Fin (N + 1)) := integral_ionization_selected_repulsion_le_defect
    ε hε i (finSuccAboveEquiv i) Z E hE u
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (N + 1)))) => hb i)
  have hc (i : Fin (N + 1)) := integral_ionization_selected_repulsion_eq_sum
    ε hε i (finSuccAboveEquiv i) u
  simp only [ionizationParticleWeight] at hc
  simp_rw [hc] at hs
  have hp := sum_ionization_ordered_pairs_eq_increasing ε hε u
  simp only [ionizationParticleWeight] at hp
  rw [hp] at hs
  rw [Finset.sum_add_distrib,
    ionization_sum_weak_defect_eq_zero (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) E u heq ε hε] at hs
  simpa only [hu, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, zero_add, ionizationParticleWeight] using hs

end LiebThirring
end
