/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalPacking

/-!
# Renewal convergence for the canonical ball sequence

Argument renewal convergence specialized to the physical recurrence of canonical recurrence. The
translation, integer-packing, and stability inputs remain explicit.
-/

@[expose] public section

open Filter Finset Metric Set Topology
open scoped NNReal

namespace LiebThirring.ThermoLimit

/-- The canonical sequence converges at each nonnegative density, with the
renewal convergence bounds and defect/majorant conclusions. -/
theorem canonicalBallSequence_convergence {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ e : ℝ,
      Tendsto (canonicalBallSequence E ρ) atTop (𝓝 e) ∧
      -A * ρ ≤ e ∧ e ≤ (1 / 28 : ℝ) * canonicalBallSequence E ρ 0 ∧
      (∀ n, 0 ≤ renewalDefect (canonicalBallSequence E ρ)
        (1 / 28 : ℝ) swissCheeseGamma n) ∧
      Tendsto (renewalDefect (canonicalBallSequence E ρ)
        (1 / 28 : ℝ) swissCheeseGamma) atTop (𝓝 0) ∧
      Antitone (renewalMajorant (canonicalBallSequence E ρ)
        (1 / 28 : ℝ) swissCheeseGamma) ∧
      Tendsto (renewalMajorant (canonicalBallSequence E ρ)
        (1 / 28 : ℝ) swissCheeseGamma) atTop (𝓝 e) ∧
      ∀ n, renewalMajorant (canonicalBallSequence E ρ)
          (1 / 28 : ℝ) swissCheeseGamma n =
        canonicalBallSequence E ρ (n + 1) +
          renewalDefect (canonicalBallSequence E ρ)
            (1 / 28 : ℝ) swissCheeseGamma n := by
  apply renewal_convergence (canonicalBallSequence E ρ)
    (1 / 28 : ℝ) swissCheeseGamma (-A * ρ)
  · norm_num [swissCheeseGamma]
  · norm_num [swissCheeseGamma]
  · exact canonicalBallSequence_recurrence htranslation hpacking hρ
  · exact canonicalBallSequence_lower_bound hlower hρ

/-- There is a unique real-valued pointwise limit of the canonical sequence on
the nonnegative density axis. -/
theorem existsUnique_canonicalBallSequence_limit {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m) :
    ∃! e : (ℝ≥0) → ℝ, ∀ ρ : ℝ≥0,
      Tendsto (canonicalBallSequence E (ρ : ℝ)) atTop (𝓝 (e ρ)) := by
  choose e he using fun ρ : ℝ≥0 =>
    canonicalBallSequence_convergence htranslation hpacking hlower ρ.coe_nonneg
  refine ⟨e, fun ρ => (he ρ).1, ?_⟩
  intro e' he'
  funext ρ
  exact (tendsto_nhds_unique (he ρ).1 (he' ρ)).symm

/-- Any pointwise limit has the stability lower bound and the inflated-seed
upper bound. -/
theorem canonicalLimit_bounds {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    (e : ℝ → ℝ)
    (he : ∀ ρ, 0 ≤ ρ → Tendsto (canonicalBallSequence E ρ) atTop (𝓝 (e ρ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    -A * ρ ≤ e ρ ∧
      e ρ ≤ (1 / 28 : ℝ) * canonicalBallSequence E ρ 0 := by
  obtain ⟨e', he', hlo, hhi, _⟩ :=
    canonicalBallSequence_convergence htranslation hpacking hlower hρ
  have heq : e' = e ρ := tendsto_nhds_unique he' (he ρ hρ)
  simpa only [heq] using And.intro hlo hhi

/-- Canonical renewal defects tend to zero at every density. -/
theorem canonicalLimit_defect_tendsto {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (renewalDefect (canonicalBallSequence E ρ)
      (1 / 28 : ℝ) swissCheeseGamma) atTop (𝓝 0) := by
  obtain ⟨_, _, _, _, _, hdef, _⟩ :=
    canonicalBallSequence_convergence htranslation hpacking hlower hρ
  exact hdef

/-- Canonical renewal majorants decrease at every density. -/
theorem antitone_canonicalBallSequence_majorant {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    (ρ : ℝ≥0) :
    Antitone (renewalMajorant (canonicalBallSequence E (ρ : ℝ))
      (1 / 28 : ℝ) swissCheeseGamma) := by
  obtain ⟨_, _, _, _, _, _, hanti, _⟩ :=
    canonicalBallSequence_convergence htranslation hpacking hlower ρ.coe_nonneg
  exact hanti

/-- The canonical majorants converge to any specified pointwise limit. -/
theorem canonicalLimit_majorant_tendsto {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    (e : ℝ → ℝ)
    (he : ∀ ρ, 0 ≤ ρ → Tendsto (canonicalBallSequence E ρ) atTop (𝓝 (e ρ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (renewalMajorant (canonicalBallSequence E ρ)
      (1 / 28 : ℝ) swissCheeseGamma) atTop (𝓝 (e ρ)) := by
  obtain ⟨e', he', _, _, _, _, _, hmajorant, _⟩ :=
    canonicalBallSequence_convergence htranslation hpacking hlower hρ
  have heq : e' = e ρ := tendsto_nhds_unique he' (he ρ hρ)
  simpa only [heq] using hmajorant

end LiebThirring.ThermoLimit

end
