/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.UpperComparison
public import LiebThirring.ThermoBounds.LatticeFractions
import Mathlib.Tactic

/-!
# Upper bounds at arbitrary radii

Conditional interior packing comparison. The physical laws are exactly the neutral integer
packing law and the translation/domain-inclusion conclusions of rigid-motion and domain-inclusion identities.
The continuity and compact-interval uniformity inputs are the conclusions
of limit convexity and uniform convergence. Actual packing geometry is proved, rather than supplied
as an extra hypothesis. The extensive quantum stability bound is used when passing
from eventual inequalities to the real-valued `limsup`.
-/

public section

open Filter Topology Finset Metric Set
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

/-- The epsilon form of interior packing comparison, conditional only on the integer physics
and the two explicitly authorized analytic conclusions. -/
theorem eventually_arbitrary_ball_le_limit_add_of_integer_inputs
    {E : Set Position → ℕ → ℝ} {e : ℝ → ℝ}
    (hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ m, E Ω' m ≤ E Ω m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (ι : Type) (s : Finset ι) (c : ι → Position)
      (r : ι → ℝ) (m : ι → ℕ), s.Nonempty →
      (∀ i ∈ s, 0 < r i) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (⋃ i ∈ s, ball (c i) (r i)) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (he : ContinuousOn e (Ici 0))
    (huniform : ∀ (l u : ℝ), 0 ≤ l → l ≤ u → ∀ δ > 0, ∃ n₀,
      ∀ n ≥ n₀, ∀ x ∈ Set.Icc l u, |neutralStandardSequence E n x - e x| ≤ δ)
    {L : ℕ → ℝ} {m : ℕ → ℕ} {ρ : ℝ}
    (hLpos : ∀ j, 0 < L j) (hL : Tendsto L atTop atTop) (hρ : 0 < ρ)
    (hs : Tendsto (fun j => (m j : ℝ) / neutralBallVolume (L j)) atTop (𝓝 ρ)) :
    ∀ ε > 0, ∀ᶠ j in atTop, neutralBallDensity E (L j) (m j) ≤ e ρ + ε := by
  classical
  obtain ⟨ell, hell⟩ := exists_standard_lattice_sides
  let μ : ℕ → ℕ → ℝ := fun k j =>
    ballLatticeCount (ell k) (L j) (hell k).1 * (ell k) ^ 3 / neutralBallVolume (L j)
  apply eventually_le_limit_add_of_upper_comparison (μ := μ) hρ hs he huniform
  · intro k
    exact tendsto_ball_lattice_fraction (hell k).1 hL
  · intro t ht k htk
    filter_upwards [eventually_ball_lattice_count_pos (hell k).1 hL] with j hn
    have hμpos : 0 < μ k j :=
      div_pos (mul_pos (Nat.cast_pos.mpr hn) (pow_pos (hell k).1 _))
        (neutralBallVolume_pos (hLpos j))
    refine ⟨hμpos.le, ?_⟩
    have hp := finite_lattice_upper_of_integer_inputs hmono htranslation hpacking
      (hell k).1 (hLpos j) ht htk (hell k).2 (m j) hn
    have harg : (m j : ℝ) /
        (retainedFraction t * ballLatticeCount (ell k) (L j) (hell k).1 * (ell k) ^ 3) =
        ((m j : ℝ) / neutralBallVolume (L j)) / (retainedFraction t * μ k j) := by
      dsimp only [μ]
      field_simp [(neutralBallVolume_pos (hLpos j)).ne',
        (retainedFraction_pos ht).ne', (Nat.cast_pos.mpr hn :
          (0 : ℝ) < ballLatticeCount (ell k) (L j) (hell k).1).ne',
        (hell k).1.ne']
    rw [harg] at hp
    exact hp

end LiebThirring.ThermoBounds

end
