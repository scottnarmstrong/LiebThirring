/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedGraph
public import LiebThirring.Ionization.WeightedSelectedSmooth

/-! # Weighted selected-coordinate positivity on the full Fourier form domain

The compact smooth positivity theorem passes to simultaneous L² limits of
states and all weak derivatives. This applies to the carriers.
-/

public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace LiebThirring
open Sobolev

/-- Selected-coordinate weighted kinetic positivity for arbitrary finite-energy states. -/
theorem re_sum_inner_selected_ionization_weakDerivatives_nonneg {N q : ℕ}
    {ε : ℝ} (hε : 0 ≤ ε) (i : Fin N) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a))
    (B : ℝ) (hB : ∀ x : Position, ‖ionizationWeight ε ‖x‖‖ ≤ B) :
    0 ≤ (∑ a : Fin 3, inner ℂ
      (lipschitzProductDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
        B (fun _Y => hB _) 1
        (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
        (i, a) u (g (i, a))) (g (i, a))).re := by
  obtain ⟨f, hfc, hfu, hfg⟩ := exists_compact_smooth_weakDerivative_sequence u g hg
  have ht := tendsto_selected_multiplier_cross i
    (fun Y => ionizationWeight ε ‖particlePosition Y i‖) B (fun _Y => hB _) 1
    (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε)) hfu hfg
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n =>
    re_sum_inner_selected_ionization_productDerivative_nonneg hε i (f n) (hfc n) B hB)

end LiebThirring
end
