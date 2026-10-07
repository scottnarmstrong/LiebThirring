/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorCoulombReal
import LiebThirring.Sobolev.Collisions

/-! # Full-density spectator Coulomb split -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Variational

open LiebThirring.Assembly

private theorem coulombKernel_ne_top_of_ne {x y : Position} (h : x ≠ y) :
    coulombKernel x y ≠ ⊤ := by
  rw [coulombKernel_eq_of_ne h]
  exact ENNReal.ofReal_ne_top

private theorem electronRepulsion_ne_top_of_collision_free {N : ℕ} (X : Configuration N)
    (h : ∀ i j, i ≠ j → particlePosition X i ≠ particlePosition X j) :
    electronRepulsion X ≠ ⊤ := by
  unfold electronRepulsion
  rw [ENNReal.sum_ne_top]
  intro i _
  rw [ENNReal.sum_ne_top]
  intro j hj
  exact coulombKernel_ne_top_of_ne (h i j (ne_of_lt (Finset.mem_filter.mp hj).2))

private theorem attraction_ne_top_of_collision_free {N : ℕ} (X : Configuration N)
    (Z : ℝ≥0) (h : ∀ i, particlePosition X i ≠ (0 : Position)) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) X ≠ ⊤ := by
  unfold attraction
  rw [ENNReal.sum_ne_top]
  intro i _
  rw [ENNReal.sum_ne_top]
  intro k _
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (coulombKernel_ne_top_of_ne (h i))

/-- The literal residual weighted signed potential density is integrable. -/
theorem integrable_residual_weighted_potential {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (hb : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) => b (particlePosition X i) *
      ((electronRepulsion (residualProjection i e X)).toReal -
        (attraction (fun _ : Fin 1 => Z) (fun _ => 0)
          (residualProjection i e X)).toReal) * ‖(u : State (N + 1) q) X‖ ^ 2) := by
  have hr := integrable_weighted_residual_repulsion i e u b hb B hB
  have ha := integrable_weighted_residual_attraction i e Z u b hb B hB
  apply (hr.sub ha).congr
  filter_upwards with X
  dsimp only [Pi.sub_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb0 _)]
  ring

/-- The literal selected-interaction weighted signed potential density is integrable. -/
theorem integrable_selected_weighted_potential {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (hb : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) => b (particlePosition X i) *
      ((selectedRepulsionKernel i e X).toReal -
        ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal) *
          ‖(u : State (N + 1) q) X‖ ^ 2) := by
  have hr := integrable_weighted_selected_repulsion i e u b hb B hB
  have ha := integrable_weighted_selected_attraction i e Z u b hb B hB
  apply (hr.sub ha).congr
  filter_upwards with X
  dsimp only [Pi.sub_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb0 _)]
  ring

/-- The literal full atomic Coulomb expectation splits into residual and selected-particle
expectations. -/
theorem integral_full_weighted_potential_split {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (hb : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫ X : Configuration (N + 1), b (particlePosition X i) *
      ((electronRepulsion X).toReal -
        (attraction (fun _ : Fin 1 => Z) (fun _ => 0) X).toReal) *
          ‖(u : State (N + 1) q) X‖ ^ 2) =
      (∫ X : Configuration (N + 1), b (particlePosition X i) *
        ((electronRepulsion (residualProjection i e X)).toReal -
          (attraction (fun _ : Fin 1 => Z) (fun _ => 0)
            (residualProjection i e X)).toReal) * ‖(u : State (N + 1) q) X‖ ^ 2) +
      ∫ X : Configuration (N + 1), b (particlePosition X i) *
        ((selectedRepulsionKernel i e X).toReal -
          ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal) *
            ‖(u : State (N + 1) q) X‖ ^ 2 := by
  have hr := integrable_residual_weighted_potential i e Z u b hb hb0 B hB
  have hs := integrable_selected_weighted_potential i e Z u b hb hb0 B hB
  rw [← integral_add hr hs]
  apply integral_congr_ae
  filter_upwards [LiebThirring.Sobolev.ae_collision_free
    (N := N + 1) (fun _ : Fin 1 => (0 : Position))] with X hX
  have hrep : electronRepulsion X ≠ ⊤ :=
    electronRepulsion_ne_top_of_collision_free X hX.2
  have hattr : attraction (fun _ : Fin 1 => Z) (fun _ => 0) X ≠ ⊤ :=
    attraction_ne_top_of_collision_free X Z (fun j => hX.1 j 0)
  have hrr : electronRepulsion (residualProjection i e X) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hrep
    rw [electronRepulsion_residualProjection i e X]
    exact le_add_right le_rfl
  have hrs : selectedRepulsionKernel i e X ≠ ⊤ := by
    apply ne_top_of_le_ne_top hrep
    rw [electronRepulsion_residualProjection i e X]
    exact le_add_left le_rfl
  have har : attraction (fun _ : Fin 1 => Z) (fun _ => 0)
      (residualProjection i e X) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hattr
    rw [attraction_atom_residualProjection i e Z X]
    exact le_add_right le_rfl
  have has : (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0 ≠ ⊤ := by
    apply ne_top_of_le_ne_top hattr
    rw [attraction_atom_residualProjection i e Z X]
    exact le_add_left le_rfl
  rw [electronRepulsion_residualProjection i e X,
    attraction_atom_residualProjection i e Z X]
  rw [show (∑ j : Fin N, coulombKernel (particlePosition X i)
      (particlePosition (residualProjection i e X) j)) = selectedRepulsionKernel i e X from rfl,
    ENNReal.toReal_add hrr hrs, ENNReal.toReal_add har has]
  ring

end LiebThirring.Variational

end
