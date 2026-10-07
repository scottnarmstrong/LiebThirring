/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.PotentialRegularity

/-! # A continuous capped nuclear potential

The auxiliary potential for the neutrality and saturation's comparison argument. The cap is
used only in an ordinary library helper; the TF functional and nuclear
potential remain literal. Off the nuclei this cap decreases the true potential.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

@[expose] noncomputable def tfCappedNuclearPotential {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (δ : ℝ) (x : Position) : ℝ :=
  ∑ k, (z k : ℝ) / max δ ‖x - R k‖

theorem continuous_tfCappedNuclearPotential {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (δ : ℝ) (hδ : 0 < δ) :
    Continuous (tfCappedNuclearPotential z R δ) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_const.div
    (continuous_const.max (continuous_id.sub continuous_const).norm)
    (fun x => (hδ.trans_le (le_max_left δ ‖x - R k‖)).ne')

theorem tendsto_tfCappedNuclearPotential_zero {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (δ : ℝ) :
    Tendsto (tfCappedNuclearPotential z R δ) (Bornology.cobounded Position) (𝓝 0) := by
  have hk : ∀ k : Fin M, Tendsto (fun x : Position => (z k : ℝ) / max δ ‖x - R k‖)
      (Bornology.cobounded Position) (𝓝 0) := by
    intro k
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_mono (fun _ => le_max_right _ _)
      (tendsto_norm_cobounded_atTop.comp (tendsto_sub_const_cobounded (R k)))
  have h := tendsto_finsetSum Finset.univ (fun k _ => hk k)
  change Tendsto (fun x : Position => ∑ k, (z k : ℝ) / max δ ‖x - R k‖)
    (Bornology.cobounded Position) (𝓝 0)
  simpa only [Finset.sum_const_zero] using h

theorem tfCappedNuclearPotential_eq_of_le {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (δ : ℝ) (x : Position) (hx : ∀ k, δ ≤ ‖x - R k‖) :
    tfCappedNuclearPotential z R δ x = tfNuclearPotential z R x := by
  unfold tfCappedNuclearPotential tfNuclearPotential
  apply Finset.sum_congr rfl
  intro k _
  rw [max_eq_right (hx k)]

theorem tfCappedNuclearPotential_le_of_ne {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (δ : ℝ) (x : Position) (hx : ∀ k, x ≠ R k) :
    tfCappedNuclearPotential z R δ x ≤ tfNuclearPotential z R x := by
  unfold tfCappedNuclearPotential tfNuclearPotential
  apply Finset.sum_le_sum
  intro k _
  exact div_le_div_of_nonneg_left (z k).property
    (norm_pos_iff.mpr (sub_ne_zero.mpr (hx k))) (le_max_right _ _)

/-- A common cap exists also for no nuclei, when the finite condition is vacuous. -/
theorem exists_positive_nuclear_cap {M : ℕ} (z : Fin M → ℝ≥0)
    (hz : ∀ k, 0 < z k) (B : ℝ) (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k, B < (z k : ℝ) / δ := by
  have hB1 : 0 < B + 1 := by linarith
  have he : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k : Fin M, δ < (z k : ℝ) / (B + 1) := by
    apply (Filter.eventually_all).mpr
    intro k
    exact (eventually_lt_nhds (div_pos (by exact_mod_cast hz k) hB1)).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hd⟩ := (eventually_mem_nhdsWithin.and he).exists
  change 0 < δ at hδ
  refine ⟨δ, hδ, fun k => ?_⟩
  have h := (lt_div_iff₀ hB1).mp (hd k)
  apply (lt_div_iff₀ hδ).mpr
  nlinarith only [h, hδ]

end LiebThirring.TFMinimizer

end
