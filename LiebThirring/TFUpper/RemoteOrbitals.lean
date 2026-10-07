/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeSpinOrbital
import LiebThirring.Ionization.EscapeLimit

/-! # Finite families of remote one-particle orbitals

This module supplies the geometric part of the particle-number correction.
A fixed compact normalized bump is dilated and placed in pairwise separated
balls. The resulting spatial-spin Schwartz orbitals retain unit mass and have
an exact inverse-square kinetic scale.

Direct proof construction; source
context Lieb–Simon (1977) III.5, (74)--(78), pp. 72--73.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring.TFUpper

/-- Canonical starting point beyond a main ball of radius `R`. -/
@[expose] noncomputable def remoteStart (R L : ℝ) : Position :=
  (R + 2 * L) • (PiLp.single 2 (0 : Fin 3) (1 : ℝ) : Position)

/-- Centers separated by four dilation radii along the first coordinate. -/
@[expose] noncomputable def remoteOrbitalCenter (a : Position) (L : ℝ) (i : ℕ) : Position :=
  a + (4 * L * (i : ℝ)) • (PiLp.single 2 (0 : Fin 3) (1 : ℝ) : Position)

/-- The distance between two centers is four radii times their index separation. -/
theorem dist_remoteOrbitalCenter (a : Position) (L : ℝ) (i j : ℕ) :
    dist (remoteOrbitalCenter a L i) (remoteOrbitalCenter a L j) =
      |4 * L * ((i : ℝ) - (j : ℝ))| := by
  rw [dist_eq_norm]
  simp only [remoteOrbitalCenter, add_sub_add_left_eq_sub]
  rw [← sub_smul]
  simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  congr 1
  ring

/-- Distinct centers are more than two radii apart. -/
theorem two_mul_lt_dist_remoteOrbitalCenter (a : Position) {L : ℝ} (hL : 0 < L)
    {i j : ℕ} (hij : i ≠ j) :
    2 * L < dist (remoteOrbitalCenter a L i) (remoteOrbitalCenter a L j) := by
  rw [dist_remoteOrbitalCenter]
  have hne : (i : ℤ) - (j : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  have hnat : 1 ≤ |(i : ℤ) - (j : ℤ)| := Int.one_le_abs hne
  have hreal : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
    have hc : (1 : ℝ) ≤ ((|(i : ℤ) - (j : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hnat
    simpa only [Int.cast_abs, Int.cast_sub, Int.cast_natCast] using hc
  rw [abs_mul]
  have h4 : |4 * L| = 4 * L := abs_of_pos (mul_pos (by norm_num) hL)
  rw [h4]
  nlinarith [mul_le_mul_of_nonneg_left hreal (show 0 ≤ 4 * L by positivity)]

/-- Every radius-`L` remote ball in the canonical placement lies outside the
closed main ball of radius `R`. -/
theorem norm_gt_of_mem_remote_closedBall {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (i : ℕ) {x : Position}
    (hx : x ∈ Metric.closedBall
      (remoteOrbitalCenter (remoteStart R L) L i) L) : R < ‖x‖ := by
  have hc : ‖remoteOrbitalCenter (remoteStart R L) L i‖ =
      R + 2 * L + 4 * L * (i : ℝ) := by
    simp only [remoteOrbitalCenter, remoteStart, ← add_smul, norm_smul,
      PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    positivity
  have hdist : dist (remoteOrbitalCenter (remoteStart R L) L i) x ≤ L := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  have htri := dist_triangle (remoteOrbitalCenter (remoteStart R L) L i) x 0
  rw [dist_zero_right, dist_zero_right, hc] at htri
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hL.le) hi]

/-- A normalized compact scalar bump, dilated at a member of the remote center family
and embedded in a fixed spin channel. -/
@[expose] noncomputable def remoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) (i : ℕ) : 𝓢(Position, EuclideanSpace ℂ (Fin q)) :=
  escapeSpinOrbital (escapeOrbitalSchwartz h hh L hL (remoteOrbitalCenter a L i)) t

/-- Every member of the remote family has unit L2 norm. -/
theorem norm_toLp_remoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (hn : (∫ x, ‖h x‖ ^ 2) = 1)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    ‖(remoteSpinOrbital h hh t a L hL i).toLp 2 (volume : Measure Position)‖ = 1 := by
  unfold remoteSpinOrbital
  rw [norm_toLp_escapeSpinOrbital]
  exact norm_toLp_escapeOrbitalSchwartz h hh hn L hL _

/-- Every member is supported in its radius-`L` ball. -/
theorem tsupport_remoteSpinOrbital_subset {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) (i : ℕ) :
    tsupport (fun x => remoteSpinOrbital h hh t a L hL i x) ⊆
      Metric.closedBall (remoteOrbitalCenter a L i) L := by
  exact (tsupport_escapeSpinOrbital_subset _ t).trans
    (tsupport_escapeOrbital_subset (fun x => h x) hh L hL _)

/-- The closed supports of distinct remote orbitals are disjoint. -/
theorem disjoint_tsupport_remoteSpinOrbital {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (tsupport (fun x => remoteSpinOrbital h hh t a L hL i x))
      (tsupport (fun x => remoteSpinOrbital h hh t a L hL j x)) := by
  apply Set.disjoint_of_subset
    (tsupport_remoteSpinOrbital_subset h hh t a L hL i)
    (tsupport_remoteSpinOrbital_subset h hh t a L hL j)
  apply Metric.closedBall_disjoint_closedBall
  simpa only [two_mul] using two_mul_lt_dist_remoteOrbitalCenter a hL hij

/-- Distinct members have pointwise zero inner product.  This is the concrete
orthogonality input needed when the family is transported to one-particle states. -/
theorem inner_remoteSpinOrbital_eq_zero {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) {i j : ℕ} (hij : i ≠ j) (x : Position) :
    inner ℂ (remoteSpinOrbital h hh t a L hL i x)
      (remoteSpinOrbital h hh t a L hL j x) = 0 := by
  by_cases hi : remoteSpinOrbital h hh t a L hL i x = 0
  · simp [hi]
  · have hxi : x ∈ tsupport (fun y => remoteSpinOrbital h hh t a L hL i y) :=
      subset_tsupport _ hi
    have hxj : x ∉ tsupport (fun y => remoteSpinOrbital h hh t a L hL j y) := by
      intro hxj
      exact Set.disjoint_left.mp
        (disjoint_tsupport_remoteSpinOrbital h hh t a L hL hij) hxi hxj
    have hj : remoteSpinOrbital h hh t a L hL j x = 0 := by
      exact image_eq_zero_of_notMem_tsupport hxj
    simp [hj]

/-- Distinct members are orthogonal in the spatial L2 integral. -/
theorem integral_inner_remoteSpinOrbital_eq_zero {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) {i j : ℕ} (hij : i ≠ j) :
    (∫ x, inner ℂ (remoteSpinOrbital h hh t a L hL i x)
      (remoteSpinOrbital h hh t a L hL j x)) = 0 := by
  simp only [inner_remoteSpinOrbital_eq_zero h hh t a L hL hij, integral_zero]

/-- Exact full kinetic scaling for each member of the family. -/
theorem sum_integral_norm_sq_fderiv_remoteSpinOrbital {q : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    (∑ k : Fin 3, ∫ x, ‖fderiv ℝ
      (fun y => remoteSpinOrbital h hh t a L hL i y) x
        (PiLp.single 2 k (1 : ℝ))‖ ^ 2) =
      L⁻¹ ^ 2 * ∑ k : Fin 3, ∫ x, ‖fderiv ℝ (fun y => h y) x
        (PiLp.single 2 k (1 : ℝ))‖ ^ 2 := by
  unfold remoteSpinOrbital
  simp only [integral_norm_sq_fderiv_escapeSpinOrbital]
  exact sum_integral_norm_sq_fderiv_escapeOrbital (fun x => h x) (h.smooth ⊤) L hL _

/-- The kinetic sum of an `r`-member remote family has the exact expected scale. -/
theorem sum_remoteSpinOrbital_kinetic {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    (∑ i : Fin r, ∑ k : Fin 3, ∫ x, ‖fderiv ℝ
      (fun y => remoteSpinOrbital h hh t a L hL i y) x
        (PiLp.single 2 k (1 : ℝ))‖ ^ 2) =
      (r : ℝ) * (L⁻¹ ^ 2 * ∑ k : Fin 3, ∫ x, ‖fderiv ℝ (fun y => h y) x
        (PiLp.single 2 k (1 : ℝ))‖ ^ 2) := by
  simp only [sum_integral_norm_sq_fderiv_remoteSpinOrbital]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end LiebThirring.TFUpper

end
