/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.StrictGeometry
public import LiebThirring.Ionization.PairInequalityLimit
import LiebThirring.Ionization.StrictIntegral

/-!
# Strict pair expectation for normalized states

The geometric exceptional set has zero configuration volume and
therefore cannot carry the mass of a normalized L² state. Strictness uses no
strict inequality between the eigenvalue and the escape threshold.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace LiebThirring

/-- Real squared mass of a state, on the configuration carrier. -/
theorem integral_strict_state_norm_sq {N q : ℕ} (u : State N q) :
    (∫ X, ‖u X‖ ^ 2) = ‖u‖ ^ 2 := by
  have hi := (Lp.memLp u).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hh := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun X => sq_nonneg ‖u X‖))
  have hc : (∫⁻ X, ENNReal.ofReal (‖u X‖ ^ 2)) =
      (‖u‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← lintegral_state_norm_sq]
    apply lintegral_congr
    intro X
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  rw [hc] at hh
  have ht := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun X => sq_nonneg ‖u X‖)),
    ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using ht

/-- The pair ratio is strictly larger than one a.e. for distinct particle labels. -/
theorem ae_one_lt_ionizationPairRatio {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ X : Configuration N, 1 < ionizationPairRatio i j X := by
  filter_upwards [ae_particlePosition_norm_sub_lt_add i j hij,
    Sobolev.ae_particlePosition_ne_particlePosition i j hij] with X ht hn
  exact (one_lt_div (norm_pos_iff.mpr (sub_ne_zero.mpr hn))).mpr ht

/-- The number of unordered electron pairs, cast to the reals. -/
theorem card_ionizationPairs_real (N : ℕ) :
    ((ionizationPairs N).card : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  have hc : (ionizationPairs N).card = N.choose 2 := by
    simpa only [ionizationPairs, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))
  rw [hc, Nat.cast_choose_two]

/-- There is an unordered pair as soon as there are at least two particles. -/
theorem ionizationPairs_nonempty {N : ℕ} (hN : 2 ≤ N) : (ionizationPairs N).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp only [ionizationPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    and_self, true_and]
  exact Nat.zero_lt_one

/-- A normalized state has a strictly larger total pair expectation than the pair count. -/
theorem pair_count_lt_integral_ionizationPairRatio {N q : ℕ} (hN : 2 ≤ N)
    (u : State N q) (hu : ‖u‖ = 1)
    (hi : Integrable (fun X => ∑ p ∈ ionizationPairs N,
      ionizationPairRatio p.1 p.2 X * ‖u X‖ ^ 2)) :
    (N : ℝ) * ((N : ℝ) - 1) / 2 <
      ∫ X, ∑ p ∈ ionizationPairs N, ionizationPairRatio p.1 p.2 X * ‖u X‖ ^ 2 := by
  have hs : ∀ᵐ X : Configuration N, ((ionizationPairs N).card : ℝ) <
      ∑ p ∈ ionizationPairs N, ionizationPairRatio p.1 p.2 X := by
    have hg : ∀ᵐ X : Configuration N, ∀ i j : Fin N, i ≠ j →
        1 < ionizationPairRatio i j X := by
      simp only [ae_all_iff]
      exact fun i j hij => ae_one_lt_ionizationPairRatio i j hij
    filter_upwards [hg] with X hX
    exact card_lt_sum_of_one_lt (ionizationPairs_nonempty hN)
      (fun p hp => hX p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2))
  have hi' : Integrable (fun X =>
      (∑ p ∈ ionizationPairs N, ionizationPairRatio p.1 p.2 X) * ‖u X‖ ^ 2) := by
    simpa only [Finset.sum_mul] using hi
  have hm : (∫ X, ‖u X‖ ^ 2) = 1 := by rw [integral_strict_state_norm_sq, hu, one_pow]
  have hh := const_lt_integral_mul_of_ae_lt
    ((Lp.memLp u).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    (fun X => sq_nonneg ‖u X‖) hm hi' hs
  rw [card_ionizationPairs_real] at hh
  simpa only [Finset.sum_mul] using hh

/-- Internal passage from cutoff estimates to strict pair bounds: actual integrable cutoff estimates imply the strict count bound. -/
theorem pair_count_lt_of_ionization_cutoff {N q : ℕ} (hN : 2 ≤ N)
    (u : State N q) (hu : ‖u‖ = 1) (B : ℝ)
    (hi : ∀ ε : ℝ, 0 < ε → ∀ i j : Fin N, i < j →
      Integrable (fun X => ionizationPairCutoff ε i j X * ‖u X‖ ^ 2))
    (hb : ∀ ε : ℝ, 0 < ε →
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ∫ X, ionizationPairCutoff ε i j X * ‖u X‖ ^ 2) ≤ B) :
    (N : ℝ) * ((N : ℝ) - 1) / 2 < B := by
  obtain ⟨hfin, hbound⟩ := integral_ionizationPairRatio_le_of_cutoff u B hi hb
  exact (pair_count_lt_integral_ionizationPairRatio hN u hu hfin).trans_le hbound

end LiebThirring
end
