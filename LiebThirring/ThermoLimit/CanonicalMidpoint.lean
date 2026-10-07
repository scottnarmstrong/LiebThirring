/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalPacking
public import LiebThirring.ThermoLimit.MidpointPackingGeometry
import Mathlib.Tactic

/-!
# Midpoint packing with the exact canonical defects

Limit convexity's finite-scale midpoint inequality is proved by assigning half of
every actual size class to each density. The hypotheses are still integer
neutral packing and translation invariance, rather than midpoint convexity.
-/

public section

open Finset Metric Set Filter Topology

namespace LiebThirring.ThermoLimit

theorem canonicalBallSequence_midpoint {E : Set Position → ℕ → ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (K : ℕ) :
    canonicalBallSequence E ((ρ₁ + ρ₂) / 2) (K + 1) ≤
      (canonicalBallSequence E ρ₁ (K + 1) +
        renewalDefect (canonicalBallSequence E ρ₁) (1 / 28) swissCheeseGamma K +
        canonicalBallSequence E ρ₂ (K + 1) +
        renewalDefect (canonicalBallSequence E ρ₂) (1 / 28) swissCheeseGamma K) / 2 := by
  classical
  obtain ⟨c, hc, hd⟩ := exists_standard_ball_packing K
  let s := swissCheeseLevels (K + 1)
  let r := fun i : SwissCheeseLabel => (28 : ℝ) ^ (K - i.1)
  let x := halfBudget (fun h => standardBudget ballVolumeConstant ρ₁ (K - h))
    (fun h => standardBudget ballVolumeConstant ρ₂ (K - h))
  have hpos : ∀ i ∈ s, 0 < r i := fun i _ => pow_pos (by norm_num) _
  have hsub : ∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) ((28 : ℝ) ^ (K + 1)) :=
    fun i hi => ball_subset_closedBall.trans (hc i hi)
  have hx : ∀ i ∈ s, 0 ≤ x i := by
    intro i _
    dsimp [x, halfBudget]
    split_ifs
    · exact standardBudget_nonneg ballVolumeConstant_pos.le hρ₁ _
    · exact standardBudget_nonneg ballVolumeConstant_pos.le hρ₂ _
  have hp := interpolate_finset_packing s
    (E (ball (0 : Position) ((28 : ℝ) ^ (K + 1))))
    (fun i => E (ball (c i) (r i))) x hx
    (fun m => hpacking _ s c r m (pow_pos (by norm_num) _) hpos hsub hd)
  have he : ∀ i : SwissCheeseLabel,
      E (ball (c i) ((28 : ℝ) ^ (K - i.1))) =
        E (ball (0 : Position) ((28 : ℝ) ^ (K - i.1))) := by
    intro i
    funext m
    exact htranslation _ _ (pow_pos (by norm_num) _) m
  change interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (K + 1))))
    (∑ i ∈ swissCheeseLevels (K + 1), x i) ≤
      ∑ i ∈ swissCheeseLevels (K + 1),
        interpolate (E (ball (c i) ((28 : ℝ) ^ (K - i.1)))) (x i) at hp
  simp_rw [he] at hp
  have hsumx := sum_standard_halfBudget ballVolumeConstant_pos ρ₁ ρ₂ K
  rw [show (∑ i ∈ swissCheeseLevels (K + 1), x i) =
    ((ρ₁ + ρ₂) / 2) * standardVolume ballVolumeConstant (K + 1) from hsumx] at hp
  have hsume : (∑ i ∈ swissCheeseLevels (K + 1),
      interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (K - i.1)))) (x i)) =
      ∑ i ∈ swissCheeseLevels (K + 1),
        halfBudget
          (fun h => canonicalInterpolated E (K - h) (standardBudget ballVolumeConstant ρ₁ (K - h)))
          (fun h => canonicalInterpolated E (K - h) (standardBudget ballVolumeConstant ρ₂ (K - h))) i := by
    apply sum_congr rfl
    intro i _
    dsimp [x, halfBudget, canonicalInterpolated]
    split_ifs <;> rfl
  rw [hsume, sum_halfBudget] at hp
  have henergy (ρ : ℝ) :
      (∑ h ∈ range (K + 1), (swissCheeseMultiplicity h : ℝ) *
        canonicalInterpolated E (K - h) (standardBudget ballVolumeConstant ρ (K - h))) =
      (canonicalBallSequence E ρ (K + 1) +
        renewalDefect (canonicalBallSequence E ρ) (1 / 28) swissCheeseGamma K) *
          standardVolume ballVolumeConstant (K + 1) := by
    rw [sum_sizeClass_standard (fun j => canonicalInterpolated E j
      (standardBudget ballVolumeConstant ρ j)) K]
    have hh := standardSequence_weighted_sum (F := canonicalInterpolated E)
      (ρ := ρ) ballVolumeConstant_pos K
    have hcount : (∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K - j) : ℝ) *
        canonicalInterpolated E j (standardBudget ballVolumeConstant ρ j)) =
      ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K + 1 - j - 1) : ℝ) *
        canonicalInterpolated E j (standardBudget ballVolumeConstant ρ j) := by
      apply sum_congr rfl
      intro j _
      have hj : K + 1 - j - 1 = K - j := by omega
      rw [hj]
    rw [hcount, hh]
    simp only [canonicalBallSequence, renewalDefect]
    ring
  rw [henergy ρ₁, henergy ρ₂] at hp
  change canonicalInterpolated E (K + 1)
    (((ρ₁ + ρ₂) / 2) * standardVolume ballVolumeConstant (K + 1)) ≤ _ at hp
  change standardSequence (canonicalInterpolated E) ballVolumeConstant ((ρ₁ + ρ₂) / 2)
    (K + 1) ≤ _
  unfold standardSequence
  rw [standardBudget_succ]
  apply (div_le_iff₀ (standardVolume_pos ballVolumeConstant_pos _)).2
  convert hp using 1
  ring

end LiebThirring.ThermoLimit

end
