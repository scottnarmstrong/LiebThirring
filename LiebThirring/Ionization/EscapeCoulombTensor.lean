/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeTensor
public import LiebThirring.Ionization.EscapePotential
public import LiebThirring.Ionization.EscapeGeometry
import LiebThirring.Assembly.Coulomb
import LiebThirring.Kinetic.DensityBasic
import LiebThirring.Kinetic.Permutation

/-! # Coulomb bounds for a remote tensor summand -/

public section

open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

private theorem measurable_attraction' {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : Measurable (attraction z R : Configuration N → ℝ≥0∞) := by
  unfold attraction
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((measurable_particlePosition i).sub measurable_const).norm.ennreal_ofReal.inv

private theorem schwartz_configuration_lintegral_norm_sq_eq_one {N q : ℕ}
    (g : 𝓢(Configuration N, SpinAmplitudes N q))
    (hg : ‖g.toLp 2 (volume : Measure (Configuration N))‖ = 1) :
    (∫⁻ x : Configuration N, (‖g x‖₊ : ℝ≥0∞) ^ 2) = 1 := by
  calc
    _ = ∫⁻ x : Configuration N,
        (‖(g.toLp 2 (volume : Measure (Configuration N))) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [g.coeFn_toLp 2 (volume : Measure (Configuration N))] with x hx
      rw [hx]
    _ = (‖g.toLp 2 (volume : Measure (Configuration N))‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_state_norm_sq _
    _ = 1 := by
      have hgn : ‖g.toLp 2 (volume : Measure (Configuration N))‖₊ = 1 :=
        NNReal.coe_injective hg
      rw [hgn, ENNReal.coe_one, one_pow]

private theorem schwartz_position_lintegral_norm_sq_eq_one {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hg : ‖g.toLp 2 (volume : Measure Position)‖ = 1) :
    (∫⁻ x : Position, (‖g x‖₊ : ℝ≥0∞) ^ 2) = 1 := by
  have hlp : (∫⁻ x : Position,
      (‖(g.toLp 2 (volume : Measure Position)) x‖₊ : ℝ≥0∞) ^ 2) =
      (‖g.toLp 2 (volume : Measure Position)‖₊ : ℝ≥0∞) ^ 2 := by
    have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (Lp.aestronglyMeasurable (g.toLp 2 (volume : Measure Position)))
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← Lp.enorm_def, enorm_eq_nnnorm] using he.symm
  calc
    _ = ∫⁻ x : Position,
        (‖(g.toLp 2 (volume : Measure Position)) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [g.coeFn_toLp 2 (volume : Measure Position)] with x hx
      rw [hx]
    _ = (‖g.toLp 2 (volume : Measure Position)‖₊ : ℝ≥0∞) ^ 2 := hlp
    _ = 1 := by
      have hgn : ‖g.toLp 2 (volume : Measure Position)‖₊ = 1 := NNReal.coe_injective hg
      rw [hgn, ENNReal.coe_one, one_pow]

private theorem escape_repulsion_pointwise_le {N q : ℕ}
    (f : Configuration N → SpinAmplitudes N q)
    (h : Position → EuclideanSpace ℂ (Fin q)) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L)
    (hf : ∀ y ∈ tsupport f, ∀ j, ‖particlePosition y j‖ ≤ R)
    (hh : ∀ p ∈ tsupport h, ‖p - escapeCenter R L‖ ≤ L)
    (x : Configuration (N + 1)) :
    electronRepulsion x *
        (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 ≤
      (electronRepulsion (escapeOmitPositions 0 x) +
        (N : ℝ≥0∞) * (ENNReal.ofReal (3 * L))⁻¹) *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
  by_cases hz : escapeWedgeTermAmplitudes f h 0 x = 0
  · norm_num [hz]
  · have hpot : electronRepulsion x ≤ electronRepulsion (escapeOmitPositions 0 x) +
        (N : ℝ≥0∞) * (ENNReal.ofReal (3 * L))⁻¹ := by
      rw [← escapeInsertPositions_particlePosition_omit x,
        electronRepulsion_escapeInsertPositions]
      rw [escapeOmitPositions_escapeInsertPositions]
      suffices hmixed : (∑ j : Fin N,
          coulombKernel (particlePosition x 0)
            (particlePosition (escapeOmitPositions 0 x) j)) ≤
          (N : ℝ≥0∞) * (ENNReal.ofReal (3 * L))⁻¹ by
        simpa only [add_comm] using
          add_le_add_left hmixed (electronRepulsion (escapeOmitPositions 0 x))
      have hprod := escapeWedgeTerm_zero_norm_sq_insert f h
        (particlePosition x 0) (escapeOmitPositions 0 x)
      rw [escapeInsertPositions_particlePosition_omit] at hprod
      have hfn : f (escapeOmitPositions 0 x) ≠ 0 := by
        intro hzero
        rw [hzero, norm_zero, zero_pow (by decide), zero_mul] at hprod
        exact hz (norm_eq_zero.mp (sq_eq_zero_iff.mp hprod))
      have hhn : h (particlePosition x 0) ≠ 0 := by
        intro hzero
        rw [hzero, norm_zero, zero_pow (by decide), mul_zero] at hprod
        exact hz (norm_eq_zero.mp (sq_eq_zero_iff.mp hprod))
      have hmixed := escape_mixed_repulsion_le hR hL
        (fun j => particlePosition (escapeOmitPositions 0 x) j)
        (fun j => hf _ (subset_closure hfn) j) (hh _ (subset_closure hhn))
      simpa only [coulombKernel, norm_sub_rev] using hmixed
    simpa only [mul_comm] using
      mul_le_mul_right hpot ((‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2)

/-- The selected-zero tensor's electron repulsion is the old expectation plus at most
`N / (3L)` when both factors have unit squared mass and separated supports. -/
theorem escapeWedgeTerm_zero_lintegral_electronRepulsion_le {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L)
    (hf : ∀ y ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition y j‖ ≤ R)
    (hh : ∀ p ∈ tsupport (fun p => h p), ‖p - escapeCenter R L‖ ≤ L)
    (hmf : (∫⁻ y : Configuration N, (‖f y‖₊ : ℝ≥0∞) ^ 2) = 1)
    (hmh : (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) = 1) :
    (∫⁻ x : Configuration (N + 1), electronRepulsion x *
      (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2) ≤
      (∫⁻ y : Configuration N, electronRepulsion y * (‖f y‖₊ : ℝ≥0∞) ^ 2) +
        ENNReal.ofReal ((N : ℝ) / (3 * L)) := by
  let C : ℝ≥0∞ := (N : ℝ≥0∞) * (ENNReal.ofReal (3 * L))⁻¹
  calc
    _ ≤ ∫⁻ x : Configuration (N + 1),
        (electronRepulsion (escapeOmitPositions 0 x) + C) *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (escape_repulsion_pointwise_le f h hR hL hf hh)
    _ = (∫⁻ x : Configuration (N + 1), electronRepulsion (escapeOmitPositions 0 x) *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2) +
        ∫⁻ x : Configuration (N + 1), C *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
      simp_rw [add_mul]
      rw [lintegral_add_left]
      exact (Assembly.measurable_electronRepulsion.comp
        (contDiff_escapeOmitPositions 0).continuous.measurable).mul
        ((contDiff_escapeWedgeTermAmplitudes f h (f.smooth ⊤) (h.smooth ⊤) 0).continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
    _ = (∫⁻ y : Configuration N, electronRepulsion y * (‖f y‖₊ : ℝ≥0∞) ^ 2) + C := by
      rw [escapeWedgeTerm_zero_lintegral_old_weight f f.continuous.measurable h
          h.continuous.measurable electronRepulsion Assembly.measurable_electronRepulsion,
        hmh, one_mul, lintegral_const_mul,
        escapeWedgeTerm_lintegral_mass f f.continuous.measurable h
          h.continuous.measurable 0,
        hmh, hmf, one_mul, mul_one]
      exact (contDiff_escapeWedgeTermAmplitudes f h (f.smooth ⊤) (h.smooth ⊤) 0).continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2
    _ = _ := by
      congr 1
      unfold C
      rw [ENNReal.ofReal_div_of_pos (mul_pos (by norm_num) hL),
        ENNReal.ofReal_natCast]
      rfl

/-- Norm-one wrapper for `escapeWedgeTerm_zero_lintegral_electronRepulsion_le`. -/
theorem escapeWedgeTerm_zero_lintegral_electronRepulsion_le_of_norm {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L)
    (hf : ∀ y ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition y j‖ ≤ R)
    (hh : ∀ p ∈ tsupport (fun p => h p), ‖p - escapeCenter R L‖ ≤ L)
    (hnf : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (hnh : ‖h.toLp 2 (volume : Measure Position)‖ = 1) :
    (∫⁻ x : Configuration (N + 1), electronRepulsion x *
      (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2) ≤
      (∫⁻ y : Configuration N, electronRepulsion y * (‖f y‖₊ : ℝ≥0∞) ^ 2) +
        ENNReal.ofReal ((N : ℝ) / (3 * L)) :=
  escapeWedgeTerm_zero_lintegral_electronRepulsion_le f h hR hL hf hh
    (schwartz_configuration_lintegral_norm_sq_eq_one f hnf)
    (schwartz_position_lintegral_norm_sq_eq_one h hnh)

/-- The selected-zero tensor's atomic attraction dominates the old attraction when both
factors have unit squared mass. -/
theorem escapeWedgeTerm_zero_lintegral_attraction_ge {N q : ℕ}
    (Z : ℝ≥0) (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hmh : (∫⁻ p : Position, (‖h p‖₊ : ℝ≥0∞) ^ 2) = 1) :
    (∫⁻ y : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) y * (‖f y‖₊ : ℝ≥0∞) ^ 2) ≤
      ∫⁻ x : Configuration (N + 1),
        attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x : Configuration (N + 1),
        attraction (fun _ : Fin 1 => Z) (fun _ => 0) (escapeOmitPositions 0 x) *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [escapeWedgeTerm_zero_lintegral_old_weight f f.continuous.measurable h
          h.continuous.measurable _ (measurable_attraction' _ _), hmh, one_mul]
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      have hpot : attraction (fun _ : Fin 1 => Z) (fun _ => 0)
          (escapeOmitPositions 0 x) ≤ attraction (fun _ : Fin 1 => Z) (fun _ => 0) x := by
        rw [← escapeInsertPositions_particlePosition_omit x,
          attraction_escapeInsertPositions_atom]
        exact le_add_right le_rfl
      simpa only [mul_comm] using
        mul_le_mul_right hpot ((‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2)

/-- Norm-one wrapper for `escapeWedgeTerm_zero_lintegral_attraction_ge`. -/
theorem escapeWedgeTerm_zero_lintegral_attraction_ge_of_norm {N q : ℕ}
    (Z : ℝ≥0) (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hnh : ‖h.toLp 2 (volume : Measure Position)‖ = 1) :
    (∫⁻ y : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) y * (‖f y‖₊ : ℝ≥0∞) ^ 2) ≤
      ∫⁻ x : Configuration (N + 1),
        attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
          (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 :=
  escapeWedgeTerm_zero_lintegral_attraction_ge Z f h
    (schwartz_position_lintegral_norm_sq_eq_one h hnh)

/-- Every wedge summand has the same electron-repulsion expectation as the selected-zero term. -/
theorem escapeWedgeTerm_lintegral_electronRepulsion_eq {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (i : Fin (N + 1)) :
    (∫⁻ x : Configuration (N + 1), electronRepulsion x *
      (‖escapeWedgeTermAmplitudes f h i x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration (N + 1), electronRepulsion x *
        (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x : Configuration (N + 1),
        electronRepulsion (permutePositions (Equiv.swap 0 i) x) *
          (‖escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [electronRepulsion_permutePositions]
      congr 1
      exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞) ^ 2)
        (NNReal.coe_injective (escapeWedgeTermAmplitudes_norm_swap f h i x))
    _ = _ := (measurePreserving_permutePositions (Equiv.swap 0 i)).lintegral_comp_emb
      (measurableEmbedding_permutePositions (Equiv.swap 0 i))
      (fun x => electronRepulsion x *
        (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2)

/-- Every wedge summand has the same atomic-attraction expectation as the selected-zero term. -/
theorem escapeWedgeTerm_lintegral_attraction_eq {N q : ℕ}
    (Z : ℝ≥0) (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (i : Fin (N + 1)) :
    (∫⁻ x : Configuration (N + 1), attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
      (‖escapeWedgeTermAmplitudes f h i x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Configuration (N + 1), attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
        (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x : Configuration (N + 1),
        attraction (fun _ : Fin 1 => Z) (fun _ => 0)
            (permutePositions (Equiv.swap 0 i) x) *
          (‖escapeWedgeTermAmplitudes f h 0 (permutePositions (Equiv.swap 0 i) x)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [attraction_permutePositions]
      congr 1
      exact congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞) ^ 2)
        (NNReal.coe_injective (escapeWedgeTermAmplitudes_norm_swap f h i x))
    _ = _ := (measurePreserving_permutePositions (Equiv.swap 0 i)).lintegral_comp_emb
      (measurableEmbedding_permutePositions (Equiv.swap 0 i))
      (fun x => attraction (fun _ : Fin 1 => Z) (fun _ => 0) x *
        (‖escapeWedgeTermAmplitudes f h 0 x‖₊ : ℝ≥0∞) ^ 2)

end LiebThirring

end
