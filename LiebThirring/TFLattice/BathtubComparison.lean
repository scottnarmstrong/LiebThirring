/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OccupationCells
public import LiebThirring.TFLattice.OctantMoment

/-!
# Sharp continuous lower bound for a finite lattice occupation

The occupation-cell density lies between zero and q. Filling the positive
octant ball of the same mass minimizes its squared moment. The proof compares
`(norm²-r²)` pointwise and cancels the equal masses. Source: Lieb–Simon (1977) III.13,
pp. 67–69 (sharp eigenvalue sums).
-/

public section

open MeasureTheory Set Filter

namespace LiebThirring.TFLattice

theorem integrable_octantBall_const (r c : ℝ) :
    Integrable ((octantBall r).indicator fun _ => c) :=
  (integrableOn_const (volume_octantBall_ne_top r) (by exact enorm_ne_top)).integrable_indicator
    (measurableSet_octantBall r)

theorem integral_octantBall_const {r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    (∫ x, (octantBall r).indicator (fun _ => c) x) = c * (Real.pi / 6 * r ^ 3) := by
  rw [integral_indicator (measurableSet_octantBall r), setIntegral_const,
    volume_real_octantBall hr, smul_eq_mul, mul_comm]

theorem norm_sq_mul_octantBall_const (r c : ℝ) :
    (fun x => ‖x‖ ^ 2 * (octantBall r).indicator (fun _ => c) x) =
      (octantBall r).indicator (fun x => c * ‖x‖ ^ 2) := by
  classical
  ext x
  by_cases hx : x ∈ octantBall r <;> simp [hx, mul_comm]

theorem integrable_norm_sq_mul_octantBall_const (r c : ℝ) :
    Integrable (fun x => ‖x‖ ^ 2 * (octantBall r).indicator (fun _ => c) x) := by
  rw [norm_sq_mul_octantBall_const]
  have hi : IntegrableOn (fun x : Position => c * ‖x‖ ^ 2) (octantBall r) :=
    (integrableOn_octantBall_norm_sq r).const_mul c
  exact hi.integrable_indicator (measurableSet_octantBall r)

theorem integral_norm_sq_mul_octantBall_const {r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    (∫ x, ‖x‖ ^ 2 * (octantBall r).indicator (fun _ => c) x) =
      c * (Real.pi / 10 * r ^ 5) := by
  rw [norm_sq_mul_octantBall_const, integral_indicator (measurableSet_octantBall r),
    integral_const_mul, integral_octantBall_norm_sq hr]

/-- Conditional radius parametrization; the equal-mass radius is supplied
explicitly by the first-n theorem. There is no spectral premise. -/
theorem integral_norm_sq_mul_occupationCells_ge {q : ℕ} (s : Finset (ModeIndex q))
    {r : ℝ} (hr : 0 ≤ r) (hmass : (q : ℝ) * (Real.pi / 6 * r ^ 3) = s.card) :
    (q : ℝ) * (Real.pi / 10 * r ^ 5) ≤ ∫ x, ‖x‖ ^ 2 * occupationCells s x := by
  let g : Position → ℝ := (octantBall r).indicator fun _ => (q : ℝ)
  have hf := integrable_occupationCells s
  have hfg := integrable_norm_sq_mul_occupationCells s
  have hg : Integrable g := integrable_octantBall_const r q
  have hgg : Integrable (fun x => ‖x‖ ^ 2 * g x) :=
    integrable_norm_sq_mul_octantBall_const r q
  have hp (x : Position) :
      ‖x‖ ^ 2 * g x - r ^ 2 * g x ≤
        ‖x‖ ^ 2 * occupationCells s x - r ^ 2 * occupationCells s x := by
    classical
    by_cases hx : x ∈ octantBall r
    · have hb : ‖x‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx.2 2
      have hle := occupationCells_le s x
      have hmul := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hle)
      simp only [g, indicator_of_mem hx]
      nlinarith only [hmul]
    · simp only [g, indicator_of_notMem hx, mul_zero, sub_zero]
      by_cases ho : ∀ i, 0 ≤ x i
      · have hn : r ≤ ‖x‖ := le_of_not_gt fun h => hx ⟨ho, h.le⟩
        have hb : r ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hr hn 2
        have hmul := mul_nonneg (sub_nonneg.mpr hb) (occupationCells_nonneg s x)
        nlinarith only [hmul]
      · rw [occupationCells_zero_of_not_octant s ho]
        simp
  have hi := integral_mono (hgg.sub (hg.const_mul (r ^ 2)))
    (hfg.sub (hf.const_mul (r ^ 2))) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hgg (hg.const_mul (r ^ 2)),
    integral_sub hfg (hf.const_mul (r ^ 2)), integral_const_mul, integral_const_mul,
    integral_occupationCells, integral_norm_sq_mul_octantBall_const hr,
    integral_octantBall_const hr, hmass] at hi
  exact (sub_le_sub_iff_right _).mp hi

end LiebThirring.TFLattice

end
