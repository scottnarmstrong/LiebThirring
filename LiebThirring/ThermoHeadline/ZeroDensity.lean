/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.Energy
public import LiebThirring.ThermoLimit.Residual

/-!
# Zero-density neutral energy

Arbitrary-sequence convergence uses the actual interior unit-ball lattice capacity, extensive stability,
and the integer neutral packing law. Packing is invoked only on positive-radius
balls, so the input imposes no law on empty ambient domains.
-/

public section

open Filter Topology Metric Set Finset
open LiebThirring.ThermoBounds LiebThirring.ThermoLimit

namespace LiebThirring.ThermoHeadline

/-- Every zero-density sequence has vanishing normalized neutral energy. The
only physics inputs are extensive stability, translation invariance and the
integer neutral packing inequality on admissible domains. -/
theorem neutralBallDensity_zero_of_integer_physics
    {E : Set Position → ℕ → ℝ} {A : ℝ}
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E Ω (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    {L : ℕ → ℝ} {m : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hm : Tendsto (fun j => (m j : ℝ) / neutralBallVolume (L j)) atTop (𝓝 0)) :
    Tendsto (fun j => neutralBallDensity E (L j) (m j)) atTop (𝓝 0) := by
  have hlo := hm.const_mul (-A)
  have hhi := hm.const_mul (E (ball (0 : Position) 1) 1)
  simp only [mul_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hL.eventually (eventually_gt_atTop 0)] with j hLj
    exact neutralBallDensity_lower_bound hlower hLj (m j)
  · filter_upwards [hL.eventually (eventually_gt_atTop 0),
      eventually_residual_le_ballLatticeCount hL hm] with j hLj hcap
    have hp : ∀ (s : Finset LatticeIndex) (n : LatticeIndex → ℕ),
        (∀ i ∈ s, ball (latticeCenter 2 i) 1 ⊆ ball (0 : Position) (L j)) →
        (s : Set LatticeIndex).PairwiseDisjoint
          (fun i => ball (latticeCenter 2 i) 1) →
        E (ball (0 : Position) (L j)) (∑ i ∈ s, n i) ≤
          ∑ i ∈ s, E (ball (0 : Position) 1) (n i) := by
      intro s n hsub hdisj
      calc
        _ ≤ ∑ i ∈ s, E (ball (latticeCenter 2 i) 1) (n i) :=
          hpacking LatticeIndex _ s (latticeCenter 2) (fun _ => 1) n
            isOpen_ball (nonempty_ball.mpr hLj) isBounded_ball
            (fun _ _ => by norm_num) hsub hdisj
        _ = _ := sum_congr rfl fun i _ => htranslation _ _ (by norm_num) (n i)
    have hb := residual_energy_le (F := fun R n => E (ball (0 : Position) R) n)
      hp (le_refl (E (ball (0 : Position) 1) 1)) hcap
    change E (ball (0 : Position) (L j)) (m j) / neutralBallVolume (L j) ≤ _
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hb (neutralBallVolume_pos hLj).le

end LiebThirring.ThermoHeadline

end
