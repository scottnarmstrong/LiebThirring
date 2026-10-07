/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.UpperRadii
public import LiebThirring.ThermoBounds.ComplementaryComparison
public import LiebThirring.ThermoBounds.ComplementaryFractions
public import LiebThirring.ThermoBounds.LowerLimit
import Mathlib.Tactic

/-!
# Lower bounds at arbitrary radii

Conditional lower-limit comparison. The complementary comparison of complementary packing comparison, the minimal
covering indices, and all complementary lattice fractions are constructed
in the proof. Only the integer physics laws and the conclusions of convexity and uniform convergence are hypotheses. The outer standard scale and fixed filler scale
remain distinct throughout.
-/

public section

open Filter Topology Finset Metric Set
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

theorem eventually_limit_sub_le_arbitrary_ball_of_integer_inputs
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
    ∀ ε > 0, ∀ᶠ j in atTop, e ρ - ε ≤ neutralBallDensity E (L j) (m j) := by
  classical
  obtain ⟨ell, hell⟩ := exists_standard_lattice_sides
  choose K hcover hmin using fun j => exists_standardCover_index (hLpos j)
  let W : ℕ → ℝ := fun j => neutralBallVolume (L j) / standardVolume ballVolumeConstant (K j)
  let U : ℕ → ℕ → ℝ := fun k j =>
    annulusLatticeCount (ell k) (L j) ((28 : ℝ) ^ K j) (hell k).1 * (ell k) ^ 3 /
      standardVolume ballVolumeConstant (K j)
  let η : ℕ → ℕ → ℝ := fun k j => 1 - W j - U k j
  apply eventually_limit_sub_le_of_lower_comparison
    (W := W) (U := U) (η := η) (K := K) hρ hs he huniform
  · exact tendsto_standardCover_index_atTop L K hL hcover
  · intro k
    exact tendsto_complementary_fraction_defect (hell k).1 hL hcover
  · intro k
    filter_upwards [hL.eventually (eventually_gt_atTop 1)] with j hj
    exact complementary_fractions_geometry (hell k).1 hj (hcover j) (hmin j)
  · intro t ht k htk
    filter_upwards [hL.eventually (eventually_gt_atTop 1)] with j hj
    have hK : 0 < K j := standardCover_index_pos hj (hcover j) (hmin j)
    exact finite_complementary_comparison_of_integer_inputs hmono htranslation hpacking
      (hell k).1 (hLpos j) hK htk (hcover j) (hell k).2 (m j)

end LiebThirring.ThermoBounds

end
