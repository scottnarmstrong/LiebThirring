/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalSequence
public import LiebThirring.ThermoLimit.PackingInterpolation
public import LiebThirring.ThermoLimit.Renewal
import Mathlib.Tactic

/-!
# Canonical recurrence from integer neutral packing

The abstract neutral-sector energy `E Ω m` means `E(z*m,m;Ω)` for a fixed
nuclear charge. The explicit hypotheses are the ball translation equality of
rigid-motion and domain-inclusion identities, integer neutral variational
packing, and extensive quantum stability. The geometry follows from the
ball packing construction.
-/

@[expose] public section

open Finset Metric Set Filter Topology

namespace LiebThirring.ThermoLimit

/-- Exact canonical recurrence derived from integer packing, not assumed as an
extra physical premise. -/
theorem canonicalBallSequence_recurrence {E : Set Position → ℕ → ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (K : ℕ) :
    canonicalBallSequence E ρ (K + 1) ≤
      ∑ j ∈ range (K + 1), (1 / 28 : ℝ) * swissCheeseGamma ^ (K - j) *
        canonicalBallSequence E ρ j := by
  classical
  obtain ⟨c, hc, hd⟩ := exists_standard_ball_packing K
  let s := swissCheeseLevels (K + 1)
  let r := fun i : SwissCheeseLabel => (28 : ℝ) ^ (K - i.1)
  let x := fun i : SwissCheeseLabel => standardBudget ballVolumeConstant ρ (K - i.1)
  have hpos : ∀ i ∈ s, 0 < r i := fun i _ => pow_pos (by norm_num) _
  have hsub : ∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) ((28 : ℝ) ^ (K + 1)) :=
    fun i hi => ball_subset_closedBall.trans (hc i hi)
  have hp := interpolate_finset_packing s
    (E (ball (0 : Position) ((28 : ℝ) ^ (K + 1))))
    (fun i => E (ball (c i) (r i))) x
    (fun i _ => standardBudget_nonneg ballVolumeConstant_pos.le hρ _)
    (fun m => hpacking _ s c r m (pow_pos (by norm_num) _) hpos hsub hd)
  change interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (K + 1))))
    (∑ i ∈ swissCheeseLevels (K + 1), standardBudget ballVolumeConstant ρ (K - i.1)) ≤
      ∑ i ∈ swissCheeseLevels (K + 1),
        interpolate (E (ball (c i) ((28 : ℝ) ^ (K - i.1))))
          (standardBudget ballVolumeConstant ρ (K - i.1)) at hp
  rw [sum_standardBudget_labels ballVolumeConstant_pos] at hp
  have he : ∀ i : SwissCheeseLabel,
      E (ball (c i) ((28 : ℝ) ^ (K - i.1))) =
        E (ball (0 : Position) ((28 : ℝ) ^ (K - i.1))) := by
    intro i
    funext m
    exact htranslation _ _ (pow_pos (by norm_num) _) m
  simp_rw [he] at hp
  rw [sum_swissCheeseLevels_standard (fun j =>
    interpolate (E (ball (0 : Position) ((28 : ℝ) ^ j)))
      (standardBudget ballVolumeConstant ρ j)) K] at hp
  change canonicalInterpolated E (K + 1) (ρ * standardVolume ballVolumeConstant (K + 1)) ≤
    ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K - j) : ℝ) *
      canonicalInterpolated E j (standardBudget ballVolumeConstant ρ j) at hp
  apply standardSequence_recurrence_of_grouped_packing ballVolumeConstant_pos K
  calc
    _ ≤ _ := hp
    _ = _ := by
      apply sum_congr rfl
      intro j _
      have he : K + 1 - j - 1 = K - j := by omega
      rw [he]

end LiebThirring.ThermoLimit

end
