/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.TrialProduct

/-! # Dilation of joint trials into a positive-radius ball

Argument thermodynamic confined form estimates. Compact joint trials are shrunk, retaining
the two species statistics, and normalized inside the Schwartz core.
-/

public section

open MeasureTheory WithLp Set
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring

theorem norm_particlePosition_le {N : ℕ} (X : Configuration N) (i : Fin N) :
    ‖particlePosition X i‖ ≤ ‖X‖ := by
  have hs : ‖particlePosition X i‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fintype.sum_prod_type]
    change (∑ a : Fin 3, X (i, a) ^ 2) ≤ ∑ j : Fin N, ∑ a : Fin 3, X (j, a) ^ 2
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg
      (fun a _ => sq_nonneg (X (j, a)))) (Finset.mem_univ i)
  nlinarith only [hs, norm_nonneg X, norm_nonneg (particlePosition X i)]

theorem exists_compact_schwartz_joint_trial_in_ball (N M q : ℕ) (hq : 1 ≤ q)
    (L : {L : ℝ // 0 < L}) :
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q), f ≠ 0 ∧
      IsCompact (tsupport f) ∧
      tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
        Metric.ball (0 : Position) L.val) ∧
        (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)} ∧
      (∀ (σ : Equiv.Perm (Fin N)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f X s) ∧
      (∀ (τ : Equiv.Perm (Fin M)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (X.fst, permutePositions τ X.snd)) s = f X s) := by
  obtain ⟨f, hf, hc, ha, hn⟩ := exists_compact_schwartz_joint_trial N M q hq
  obtain ⟨r, hr, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let c : ℝ := r / L.val + 1
  have hcpos : 0 < c := add_pos (div_pos hr L.property) zero_lt_one
  let H : QuantumConfiguration N M ≃ₜ QuantumConfiguration N M :=
    Homeomorph.smulOfNeZero c hcpos.ne'
  have hs : ContDiff ℝ ∞ (fun X : QuantumConfiguration N M => f (c • X)) :=
    (f.smooth _).comp (contDiff_id.const_smul c)
  have hcomp : HasCompactSupport (fun X : QuantumConfiguration N M => f (c • X)) :=
    hc.comp_homeomorph H
  let g : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) := hcomp.toSchwartzMap hs
  have hts : tsupport g = H ⁻¹' tsupport f := by
    change closure (H ⁻¹' Function.support f) = H ⁻¹' closure (Function.support f)
    exact (H.preimage_closure _).symm
  refine ⟨g, ?_, hcomp, ?_, ?_, ?_⟩
  · intro hg
    apply hf
    ext X s
    have h := congrArg (fun u : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) =>
      u (H.symm X) s) hg
    change f (H (H.symm X)) s = 0 at h
    simpa only [H.apply_symm_apply, zero_apply, PiLp.zero_apply] using h
  · intro X hX
    have hx : c * ‖X‖ ≤ r := by
      have hm : H X ∈ tsupport f := by
        change X ∈ H ⁻¹' tsupport f
        rw [← hts]
        exact hX
      have h : ‖c • X‖ ≤ r := hbound (H X) hm
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos] using h
    have hrL : r < c * L.val := by
      dsimp only [c]
      rw [add_mul, div_mul_cancel₀ r L.property.ne', one_mul]
      exact lt_add_of_pos_right r L.property
    have hnorm : ‖X‖ < L.val := (mul_lt_mul_iff_right₀ hcpos).mp (hx.trans_lt hrL)
    constructor
    · intro i
      rw [Metric.mem_ball, dist_zero_right]
      exact ((norm_particlePosition_le X.fst i).trans (WithLp.norm_fst_le (Configuration N) X)).trans_lt hnorm
    · intro k
      rw [Metric.mem_ball, dist_zero_right]
      exact ((norm_particlePosition_le X.snd k).trans (WithLp.norm_snd_le (Configuration N) X)).trans_lt hnorm
  · intro σ X s
    have he : c • toLp 2 (permutePositions σ X.fst, X.snd) =
        toLp 2 (permutePositions σ (c • X).fst, (c • X).snd) := rfl
    change f (c • toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f (c • X) s
    rw [he]
    exact ha σ (c • X) s
  · intro τ X s
    have he : c • toLp 2 (X.fst, permutePositions τ X.snd) =
        toLp 2 ((c • X).fst, permutePositions τ (c • X).snd) := rfl
    change f (c • toLp 2 (X.fst, permutePositions τ X.snd)) s = f (c • X) s
    rw [he]
    exact hn τ (c • X) s

end LiebThirring

end
