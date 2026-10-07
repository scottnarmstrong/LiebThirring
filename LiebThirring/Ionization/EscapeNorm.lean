/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeTensor
public import LiebThirring.Ionization.EscapeSeparation
import LiebThirring.Fourier.Schwartz
import LiebThirring.Kinetic.DensityBasic

/-! # Exact unit normalization of the remote-orbital wedge -/

public section

open MeasureTheory WithLp Set Function
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Each tensor summand has unit L² mass when both factors do. -/
theorem escapeWedgeTermSchwartz_norm {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (hnf : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (hnh : (∫ p, ‖h p‖ ^ 2) = 1) (i : Fin (N + 1)) :
    ‖(escapeWedgeTermSchwartz f h hf hh i).toLp 2
      (volume : Measure (Configuration (N + 1)))‖ = 1 := by
  let g := escapeWedgeTermSchwartz f h hf hh i
  have he : (∫⁻ x : Configuration (N + 1), (‖g x‖₊ : ℝ≥0∞) ^ 2) = 1 := by
    change (∫⁻ x : Configuration (N + 1),
      (‖escapeWedgeTermAmplitudes (fun x => f x) (fun p => h p) i x‖₊ : ℝ≥0∞) ^ 2) = 1
    rw [escapeWedgeTerm_lintegral_mass (fun x => f x) f.continuous.measurable
      (fun p => h p) h.continuous.measurable,
      Fourier.lintegral_norm_sq_eq_ofReal_integral h, hnh, ENNReal.ofReal_one, one_mul]
    calc
      _ = ∫⁻ x : Configuration N,
          (‖(f.toLp 2 (volume : Measure (Configuration N))) x‖₊ : ℝ≥0∞) ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [f.coeFn_toLp 2 (volume : Measure (Configuration N))] with x hx
        rw [hx]
      _ = 1 := by
        rw [lintegral_state_norm_sq]
        have hn : ‖f.toLp 2 (volume : Measure (Configuration N))‖₊ = 1 :=
          NNReal.coe_injective hnf
        rw [hn, ENNReal.coe_one, one_pow]
  have hmass : (‖g.toLp 2 (volume : Measure (Configuration (N + 1)))‖₊ : ℝ≥0∞) ^ 2 = 1 := by
    rw [← lintegral_state_norm_sq]
    calc
      _ = ∫⁻ x : Configuration (N + 1), (‖g x‖₊ : ℝ≥0∞) ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [g.coeFn_toLp 2 (volume : Measure (Configuration (N + 1)))] with x hx
        rw [hx]
      _ = 1 := he
  have hr := congrArg ENNReal.toReal hmass
  simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm,
    ENNReal.toReal_one] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [one_pow] using hr)

/-- The compact smooth bundle is exactly the normalized sum of its bundled terms. -/
theorem escapeWedgeSchwartz_eq_sum {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x)) :
    escapeWedgeSchwartz f h hf hh =
      (Real.sqrt (N + 1))⁻¹ • ∑ i, escapeWedgeTermSchwartz f h hf hh i := by
  apply DFunLike.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [escapeWedgeSchwartz_apply, escapeWedge,
    smul_apply, sum_apply, PiLp.smul_apply, Complex.real_smul,
    WithLp.ofLp_sum, Finset.sum_apply]
  rfl

/-- Unit mass of the actual `1 / sqrt(N+1)` remote-orbital wedge. -/
theorem escapeWedgeSchwartz_norm {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (h : 𝓢(Position, EuclideanSpace ℂ (Fin q)))
    (hf : HasCompactSupport (fun x => f x)) (hh : HasCompactSupport (fun x => h x))
    (hnf : ‖f.toLp 2 (volume : Measure (Configuration N))‖ = 1)
    (hnh : (∫ p, ‖h p‖ ^ 2) = 1) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hRf : ∀ x ∈ tsupport (fun y => f y), ∀ j, ‖particlePosition x j‖ ≤ R)
    (hLh : ∀ y ∈ tsupport (fun p => h p), ‖y - escapeCenter R L‖ ≤ L) :
    ‖(escapeWedgeSchwartz f h hf hh).toLp 2
      (volume : Measure (Configuration (N + 1)))‖ = 1 := by
  rw [escapeWedgeSchwartz_eq_sum]
  let terms := escapeWedgeTermSchwartz f h hf hh
  have hd : Pairwise (Disjoint on fun i => tsupport (fun x => terms i x)) :=
    escape_disjoint_wedgeTermAmplitudes (fun y => f y) (fun p => h p) hR hL hRf hLh
  have hn (i : Fin (N + 1)) :
      ‖(terms i).toLp 2 (volume : Measure (Configuration (N + 1)))‖ = 1 :=
    escapeWedgeTermSchwartz_norm f h hf hh hnf hnh i
  simpa only [Nat.cast_succ] using
    escape_norm_toLp_normalized_sum (Nat.succ_pos N) terms hd hn

end LiebThirring

end
