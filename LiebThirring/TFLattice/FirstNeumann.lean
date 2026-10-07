/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.MomentEstimate
public import LiebThirring.TFLattice.FermiRadius
public import LiebThirring.TFLattice.OccupationComparison
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic

/-!
# Sharp first-n Neumann lattice moments

The lower bound uses the equal-mass octant ball. The upper bound uses an
n-element subset of a containing lattice ball, together with occupation
minimality. Partial last shells need no preferred enumeration. Source:
Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring.TFLattice

noncomputable def fermiMomentUpperConstant (q : ℕ) : ℝ :=
  (q : ℝ) * (12 * Real.pi) *
    (fermiRadiusCoefficient q ^ 4 + fermiRadiusCoefficient q ^ 3 +
      fermiRadiusCoefficient q ^ 2 + fermiRadiusCoefficient q + 1)

theorem fermiMomentUpperConstant_nonneg (q : ℕ) : 0 ≤ fermiMomentUpperConstant q := by
  unfold fermiMomentUpperConstant
  have h := fermiRadiusCoefficient_nonneg q
  positivity

theorem fourth_order_radius_bound {a u : ℝ} (ha : 0 ≤ a) (hu : 1 ≤ u) :
    (a * u) ^ 4 + (a * u) ^ 3 + (a * u) ^ 2 + a * u + 1 ≤
      (a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * u ^ 4 := by
  have h0 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have h1 : u ≤ u ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hu (by norm_num : 1 ≤ 4)
  have h2 : u ^ 2 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have h3 : u ^ 3 ≤ u ^ 4 := pow_le_pow_right₀ hu (by norm_num)
  have hm1 := mul_le_mul_of_nonneg_left h1 ha
  have hm2 := mul_le_mul_of_nonneg_left h2 (pow_nonneg ha 2)
  have hm3 := mul_le_mul_of_nonneg_left h3 (pow_nonneg ha 3)
  nlinarith only [h0, hm1, hm2, hm3]

theorem first_neumann_moment_lower {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s) :
    (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5 -
      (12 * Real.sqrt 3 + 3) * (s.card : ℝ) ^ (4 / 3 : ℝ) ≤
        ∑ p ∈ s, (squaredRadius p.1 : ℝ) := by
  by_cases hn : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hn
    simp [he, fermiRadius,
      Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  have hn1 : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hn
  let u := (s.card : ℝ) ^ (1 / 3 : ℝ)
  have hu : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hmass := fermiRadius_mass hq s.card
  have hlow := integral_norm_sq_mul_occupationCells_ge s
    (fermiRadius_nonneg q s.card) hmass
  have hhigh := (integral_norm_sq_mul_occupationCells_bounds s
    (fun p hp => neumann_occupation_radius_le hq hs hn1 hp)).2
  have he : (2 * Real.sqrt 3 * (6 * u) + 3) * (s.card : ℝ) ≤
      (12 * Real.sqrt 3 + 3) * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
    have hc := cube_root_cubed s.card
    have hp := cube_root_pow s.card 4
    change u ^ 3 = (s.card : ℝ) at hc
    change u ^ 4 = (s.card : ℝ) ^ (4 / 3 : ℝ) at hp
    have h := mul_le_mul_of_nonneg_right hu (by exact_mod_cast Nat.zero_le s.card : (0 : ℝ) ≤ s.card)
    rw [← hp, ← hc]
    rw [← hc] at h
    nlinarith only [h]
  nlinarith only [hlow, hhigh, he]

theorem first_neumann_moment_upper {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s) :
    (∑ p ∈ s, (squaredRadius p.1 : ℝ)) ≤
      (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5 +
        fermiMomentUpperConstant q * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  by_cases hn : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hn
    simp [he, fermiRadius,
      Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  have hn1 : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hn
  let r : ℝ≥0 := ⟨fermiRadius q s.card, fermiRadius_nonneg q s.card⟩
  have hcard : s.card ≤ (neumannBallModes q r).card := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hc := (card_neumannBallModes_volume_bounds q r).1
    have hm := fermiRadius_mass hq s.card
    change (q : ℝ) * (Real.pi / 6) * fermiRadius q s.card ^ 3 ≤ _ at hc
    nlinarith only [hc, hm]
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hcard
  have hmin := sum_squaredRadius_le_of_isFilled hs (fun _ _ => trivial) htc.symm
  have hsubset : (∑ p ∈ t, (squaredRadius p.1 : ℝ)) ≤
      ∑ p ∈ neumannBallModes q r, (squaredRadius p.1 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => Nat.cast_nonneg _)
  have herr := (abs_le.mp (sum_squaredRadius_neumannBallModes_error_le q r)).2
  have hp := fourth_order_radius_bound (fermiRadiusCoefficient_nonneg q)
    (show 1 ≤ (s.card : ℝ) ^ (1 / 3 : ℝ) from
      Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num))
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (q : ℝ) * (12 * Real.pi) by positivity)
  rw [cube_root_pow] at hp'
  have hbound : (q : ℝ) * (12 * Real.pi) *
      (fermiRadius q s.card ^ 4 + fermiRadius q s.card ^ 3 +
        fermiRadius q s.card ^ 2 + fermiRadius q s.card + 1) ≤
        fermiMomentUpperConstant q * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
    simpa only [fermiMomentUpperConstant, fermiRadius, mul_assoc, Nat.cast_ofNat] using hp'
  dsimp only [r, NNReal.toReal] at herr
  nlinarith only [hmin, hsubset, herr, hbound]

end LiebThirring.TFLattice

end
