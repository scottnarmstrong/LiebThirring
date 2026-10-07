/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeInsertion
public import LiebThirring.Ionization.EscapeWedgeSmooth
import LiebThirring.Kinetic.Permutation
import LiebThirring.Kinetic.DensityBasic

/-! # Exact tensor mass and weighted factorization for escape trials -/

public section

open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Fermionic signs have unit complex norm. -/
theorem norm_escapePermutationSign {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ‖escapePermutationSign σ‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp only [escapePermutationSign, h, Units.val_one, Units.val_neg,
      Int.cast_one, Int.cast_neg, norm_one, norm_neg]

/-- Exact counting-spin tensor norm at selected-zero insertion. -/
theorem escapeWedgeTerm_zero_norm_sq_insert {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (p : Position) (y : Configuration N) :
    ‖escapeWedgeTermAmplitudes f h 0 (escapeInsertPositions p y)‖ ^ 2 =
      ‖f y‖ ^ 2 * ‖h p‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, ← (escapeInsertionSpinEquiv N q).sum_comp]
  have he (z : Fin q × SpinLabels N q) :
      escapeWedgeTermAmplitudes f h 0 (escapeInsertPositions p y)
        (escapeInsertionSpinEquiv N q z) = f y z.2 * h p z.1 := by
    change escapePermutationSign (Equiv.swap 0 0) *
      f (escapeOmitPositions 0 (escapeInsertPositions p y))
        (escapeOmitSpins 0 (escapeInsertSpins z.1 z.2)) *
          h (particlePosition (escapeInsertPositions p y) 0) (escapeInsertSpins z.1 z.2 0) = _
    simp only [escapeOmitPositions_escapeInsertPositions, escapeOmitSpins_escapeInsertSpins,
      particlePosition_escapeInsertPositions_zero, escapeInsertSpins, Fin.cases_zero,
      escapePermutationSign, Equiv.swap_self, Equiv.Perm.sign_refl,
      Units.val_one, Int.cast_one, one_mul]
  simp_rw [he, norm_mul, mul_pow]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]

/-- The same tensor norm formula in extended nonnegative form. -/
theorem escapeWedgeTerm_zero_nnnorm_sq_insert {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (p : Position) (y : Configuration N) :
    (‖escapeWedgeTermAmplitudes f h 0 (escapeInsertPositions p y)‖₊ : ℝ≥0∞) ^ 2 =
      (‖f y‖₊ : ℝ≥0∞) ^ 2 * (‖h p‖₊ : ℝ≥0∞) ^ 2 := by
  have he := congrArg ENNReal.ofReal (escapeWedgeTerm_zero_norm_sq_insert f h p y)
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm] using he

/-- Permuting the selected particle to zero converts each signed summand to the seed. -/
theorem escapeWedgeTermAmplitudes_permute_swap {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (i : Fin (N + 1))
    (x : Configuration (N + 1)) (s : SpinLabels (N + 1) q) :
    escapeWedgeTermAmplitudes f h i x (permuteSpins (Equiv.swap 0 i) s) =
      escapePermutationSign (Equiv.swap 0 i) *
        escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x) s := by
  change escapePermutationSign (Equiv.swap 0 i) *
    f (escapeOmitPositions i x) (escapeOmitSpins i (permuteSpins (Equiv.swap 0 i) s)) *
      h (particlePosition x i) (permuteSpins (Equiv.swap 0 i) s i) = _
  have hs : escapeOmitSpins i (permuteSpins (Equiv.swap 0 i) s) = escapeOmitSpins 0 s := by
    funext j
    simp only [escapeOmitSpins, permuteSpins, Equiv.swap_apply_self, Equiv.swap_self,
      Equiv.refl_apply]
  have hp : escapeOmitPositions 0 (permutePositions (Equiv.swap 0 i) x) =
      escapeOmitPositions i x := by
    ext ja
    simp only [escapeOmitPositions, permutePositions, PiLp.toLp_apply,
      Equiv.swap_self, Equiv.refl_apply]
  rw [hs]
  simp only [escapeWedgeTermAmplitudes, PiLp.toLp_apply, escapeWedgeTerm, hp,
    escapePermutationSign, Equiv.swap_self, Equiv.Perm.sign_refl,
    Units.val_one, Int.cast_one, one_mul, permuteSpins, Equiv.swap_apply_right,
    particlePosition_permutePositions, Equiv.swap_apply_left, mul_assoc]

/-- Every signed summand has the seed's norm after the corresponding spatial swap. -/
theorem escapeWedgeTermAmplitudes_norm_swap {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) (i : Fin (N + 1))
    (x : Configuration (N + 1)) :
    ‖escapeWedgeTermAmplitudes f h i x‖ =
      ‖escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x)‖ := by
  have he : spinPermutationLinearIsometryEquiv (q := q) (Equiv.swap 0 i)
      (escapeWedgeTermAmplitudes f h i x) =
      escapePermutationSign (Equiv.swap 0 i) •
        escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x) := by
    ext s
    exact escapeWedgeTermAmplitudes_permute_swap f h i x s
  rw [← (spinPermutationLinearIsometryEquiv (q := q) (Equiv.swap 0 i)).norm_map,
    he, norm_smul, norm_escapePermutationSign, one_mul]

/-- A single compact smooth tensor summand, bundled independently of antisymmetry. -/
@[expose] noncomputable def escapeWedgeTermSchwartz {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (i : Fin (N + 1)) : 𝓢(Configuration (N + 1), SpinAmplitudes (N + 1) q) :=
  (hasCompactSupport_escapeWedgeTermAmplitudes (fun x => f x) (fun x => h x) hf hh i).toSchwartzMap
    (contDiff_escapeWedgeTermAmplitudes (fun x => f x) (fun x => h x)
      (f.smooth ⊤) (h.smooth ⊤) i)

/-- Old-coordinate weights factor exactly through the normalized-orbital tensor. -/
theorem escapeWedgeTerm_zero_lintegral_old_weight {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q) (hf : Measurable f)
    (h : Position → EuclideanSpace ℂ (Fin q)) (hh : Measurable h)
    (w : Configuration N → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x : Configuration (N + 1), w (escapeOmitPositions 0 x) *
      (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2) =
      (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) *
        ∫⁻ y : Configuration N, w y * (‖f y‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← (measurePreserving_escapeInsertion N).lintegral_comp_emb
    (escapeInsertionMeasurableEquiv N).measurableEmbedding]
  simp only [escapeInsertionMeasurableEquiv_apply, escapeOmitPositions_escapeInsertPositions,
    escapeWedgeTerm_zero_nnnorm_sq_insert]
  have he (z : Position × Configuration N) :
      w z.2 * ((‖f z.2‖₊ : ℝ≥0∞) ^ 2 * (‖h z.1‖₊ : ℝ≥0∞) ^ 2) =
        (‖h z.1‖₊ : ℝ≥0∞) ^ 2 * (w z.2 * (‖f z.2‖₊ : ℝ≥0∞) ^ 2) := by ring
  simp_rw [he]
  exact lintegral_prod_mul (hh.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
    (hw.mul (hf.nnnorm.coe_nnreal_ennreal.pow_const 2)).aemeasurable

/-- All summands have the same tensor mass, with no particle or spin multiplicity loss. -/
theorem escapeWedgeTerm_lintegral_mass {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q) (hf : Measurable f)
    (h : Position → EuclideanSpace ℂ (Fin q)) (hh : Measurable h) (i : Fin (N + 1)) :
    (∫⁻ x : Configuration (N + 1), (‖escapeWedgeTermAmplitudes f h i x‖₊ : ℝ≥0∞) ^ 2) =
      (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) *
        ∫⁻ y : Configuration N, (‖f y‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x : Configuration (N + 1),
        (‖escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [show ‖escapeWedgeTermAmplitudes f h i x‖₊ =
          ‖escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x)‖₊ from
        NNReal.coe_injective (escapeWedgeTermAmplitudes_norm_swap f h i x)]
    _ = ∫⁻ x : Configuration (N + 1), (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 :=
      (measurePreserving_permutePositions (Equiv.swap 0 i)).lintegral_comp_emb
        (measurableEmbedding_permutePositions (Equiv.swap 0 i))
        (fun x => (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2)
    _ = _ := by
      simpa only [one_mul] using escapeWedgeTerm_zero_lintegral_old_weight f hf h hh
        (fun _ => 1) measurable_const

end LiebThirring

end
