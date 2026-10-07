/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeCounting
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volumes of balls and spherical boundary layers

Elementary three-dimensional volume estimates used in the ball and annular lattice packings of the thermodynamic-limit argument.
-/

public section

open MeasureTheory Metric Set

namespace LiebThirring

/-- The volume of the unit ball in three dimensions. -/
@[expose] noncomputable def ballVolumeConstant : ℝ := 4 * Real.pi / 3

theorem ballVolumeConstant_pos : 0 < ballVolumeConstant := by
  unfold ballVolumeConstant
  positivity

theorem volume_ball_position (c : Position) (r : ℝ) :
    volume (ball c r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal ballVolumeConstant := by
  simp [ballVolumeConstant, mul_comm]

theorem volume_closedBall_position (c : Position) (r : ℝ) :
    volume (closedBall c r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal ballVolumeConstant := by
  simp [ballVolumeConstant, mul_comm]

theorem volume_real_ball_position (c : Position) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball c r) = ballVolumeConstant * r ^ 3 := by
  rw [Measure.real, volume_ball_position]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal ballVolumeConstant_pos.le]
  ring

theorem volume_real_closedBall_position (c : Position) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall c r) = ballVolumeConstant * r ^ 3 := by
  rw [Measure.real, volume_closedBall_position]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal ballVolumeConstant_pos.le]
  ring

/-- The inner boundary shell of a ball has volume at most `3 σ R² h`. -/
theorem volume_ball_diff_ball_le (c : Position) {R h : ℝ} (hR : 0 ≤ R)
    (hh : 0 ≤ h) (hhR : h ≤ R) :
    volume.real (ball c R \ ball c (R - h)) ≤ 3 * ballVolumeConstant * R ^ 2 * h := by
  rw [measureReal_sdiff (ball_subset_ball (sub_le_self R hh)) measurableSet_ball]
  rw [volume_real_ball_position c hR, volume_real_ball_position c (sub_nonneg.mpr hhR)]
  have hrem : 0 ≤ h ^ 2 * (3 * R - h) := by
    exact mul_nonneg (sq_nonneg h) (by linarith)
  have hpoly : R ^ 3 - (R - h) ^ 3 ≤ 3 * R ^ 2 * h := by
    nlinarith
  calc
    ballVolumeConstant * R ^ 3 - ballVolumeConstant * (R - h) ^ 3 =
        ballVolumeConstant * (R ^ 3 - (R - h) ^ 3) := by ring
    _ ≤ ballVolumeConstant * (3 * R ^ 2 * h) :=
      mul_le_mul_of_nonneg_left hpoly ballVolumeConstant_pos.le
    _ = 3 * ballVolumeConstant * R ^ 2 * h := by ring

/-- The exterior boundary shell of a closed ball has volume at most `7 σ R² h`. -/
theorem volume_closedBall_diff_closedBall_le (c : Position) {R h : ℝ} (hR : 0 ≤ R)
    (hh : 0 ≤ h) (hhR : h ≤ R) :
    volume.real (closedBall c (R + h) \ closedBall c R) ≤
      7 * ballVolumeConstant * R ^ 2 * h := by
  rw [measureReal_sdiff (closedBall_subset_closedBall (le_add_of_nonneg_right hh))
    measurableSet_closedBall (by rw [volume_closedBall_position]; finiteness)]
  rw [volume_real_closedBall_position c (add_nonneg hR hh),
    volume_real_closedBall_position c hR]
  have hh2 : h ^ 2 ≤ R * h := by
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hhR)]
  have hh3 : h ^ 3 ≤ R ^ 2 * h := by
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hhR),
      mul_nonneg hh (mul_nonneg hR (sub_nonneg.mpr hhR))]
  have hpoly : (R + h) ^ 3 - R ^ 3 ≤ 7 * R ^ 2 * h := by
    nlinarith [mul_nonneg hR hh]
  calc
    ballVolumeConstant * (R + h) ^ 3 - ballVolumeConstant * R ^ 3 =
        ballVolumeConstant * ((R + h) ^ 3 - R ^ 3) := by ring
    _ ≤ ballVolumeConstant * (7 * R ^ 2 * h) :=
      mul_le_mul_of_nonneg_left hpoly ballVolumeConstant_pos.le
    _ = 7 * ballVolumeConstant * R ^ 2 * h := by ring

/-- An open annulus, written in a form convenient for ball packings. -/
@[expose] def openAnnulus (c : Position) (L R : ℝ) : Set Position :=
  ball c R \ closedBall c L

/-- The lattice boundary layer of a ball lies in its inner spherical shell. -/
theorem latticeBoundaryLayer_ball_subset (c : Position) {R ell : ℝ} :
    latticeBoundaryLayer ell (ball c R) ⊆
      ball c R \ ball c (R - Real.sqrt 3 * ell) := by
  intro x hx
  rcases hx with ⟨hxR, y, hyR, hxy⟩
  refine ⟨hxR, ?_⟩
  simp only [mem_ball] at hxR hyR ⊢
  intro hxinner
  apply hyR
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle y x c
    _ = dist x y + dist x c := by rw [dist_comm y x]
    _ < R := by linarith

/-- The exact lattice boundary layer of an open annulus lies in the two radial shells
used in lattice boundary estimates. -/
theorem latticeBoundaryLayer_openAnnulus_subset_shells (c : Position) {L R ell : ℝ} :
    latticeBoundaryLayer ell (openAnnulus c L R) ⊆
      (ball c R \ ball c (R - Real.sqrt 3 * ell)) ∪
        (closedBall c (L + Real.sqrt 3 * ell) \ closedBall c L) := by
  intro x hx
  rcases hx with ⟨⟨hxR, hxL⟩, y, hy, hxy⟩
  simp only [openAnnulus, mem_sdiff, not_and_or, not_not] at hy
  rcases hy with hyR | hyL
  · left
    refine ⟨hxR, ?_⟩
    simp only [mem_ball] at hxR hyR ⊢
    intro hxinner
    apply hyR
    calc
      dist y c ≤ dist y x + dist x c := dist_triangle y x c
      _ = dist x y + dist x c := by rw [dist_comm y x]
      _ < R := by linarith
  · right
    refine ⟨?_, hxL⟩
    simp only [mem_closedBall] at hyL ⊢
    calc
      dist x c ≤ dist x y + dist y c := dist_triangle x y c
      _ ≤ Real.sqrt 3 * ell + L := add_le_add hxy hyL
      _ = L + Real.sqrt 3 * ell := add_comm _ _

/-- The two shells controlling an annular boundary layer satisfy an explicit volume bound. -/
theorem volume_real_annulus_boundary_shells_le (c : Position) {L R h : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (hh : 0 ≤ h) (hhL : h ≤ L) :
    volume.real ((ball c R \ ball c (R - h)) ∪
      (closedBall c (L + h) \ closedBall c L)) ≤
      7 * ballVolumeConstant * h * (R ^ 2 + L ^ 2) := by
  calc
    volume.real ((ball c R \ ball c (R - h)) ∪
        (closedBall c (L + h) \ closedBall c L)) ≤
        volume.real (ball c R \ ball c (R - h)) +
          volume.real (closedBall c (L + h) \ closedBall c L) :=
      measureReal_union_le _ _
    _ ≤ 3 * ballVolumeConstant * R ^ 2 * h +
          7 * ballVolumeConstant * L ^ 2 * h :=
      add_le_add
        (volume_ball_diff_ball_le c (hR := hL.trans hLR) hh (hhL.trans hLR))
        (volume_closedBall_diff_closedBall_le c hL hh hhL)
    _ ≤ 7 * ballVolumeConstant * h * (R ^ 2 + L ^ 2) := by
      have hcoeff : 3 * R ^ 2 + 7 * L ^ 2 ≤ 7 * (R ^ 2 + L ^ 2) := by
        nlinarith [sq_nonneg R]
      calc
        3 * ballVolumeConstant * R ^ 2 * h + 7 * ballVolumeConstant * L ^ 2 * h =
            (ballVolumeConstant * h) * (3 * R ^ 2 + 7 * L ^ 2) := by ring
        _ ≤ (ballVolumeConstant * h) * (7 * (R ^ 2 + L ^ 2)) :=
          mul_le_mul_of_nonneg_left hcoeff (mul_nonneg ballVolumeConstant_pos.le hh)
        _ = 7 * ballVolumeConstant * h * (R ^ 2 + L ^ 2) := by ring

/-- With lattice-cube diameter `h = √3 ℓ`, the annular shell loss has
constant `7 √3 σ`. -/
theorem volume_real_annulus_lattice_shells_le (c : Position) {L R ell : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (hell : 0 ≤ ell)
    (hellL : Real.sqrt 3 * ell ≤ L) :
    volume.real ((ball c R \ ball c (R - Real.sqrt 3 * ell)) ∪
      (closedBall c (L + Real.sqrt 3 * ell) \ closedBall c L)) ≤
      7 * Real.sqrt 3 * ballVolumeConstant * ell * (R ^ 2 + L ^ 2) := by
  have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    volume_real_annulus_boundary_shells_le c hL hLR (mul_nonneg hsqrt hell) hellL

/-- The normalized annular boundary loss, using `R ≥ L`. -/
theorem annulus_lattice_shell_normalized_le {L R ell : ℝ} (hL : 0 < L)
    (hLR : L ≤ R) (hell : 0 ≤ ell) :
    (7 * Real.sqrt 3 * ballVolumeConstant * ell * (R ^ 2 + L ^ 2)) /
        (ballVolumeConstant * R ^ 3) ≤
      14 * Real.sqrt 3 * ell / L := by
  have hR : 0 < R := hL.trans_le hLR
  have hsigma : 0 < ballVolumeConstant := ballVolumeConstant_pos
  have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hL2R2 : L ^ 2 ≤ R ^ 2 := by nlinarith
  have hLR3 : L * R ^ 2 ≤ R ^ 3 := by
    calc
      L * R ^ 2 ≤ R * R ^ 2 := mul_le_mul_of_nonneg_right hLR (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hL3R3 : L ^ 3 ≤ R ^ 3 := by
    calc
      L ^ 3 = L * L ^ 2 := by ring
      _ ≤ L * R ^ 2 := mul_le_mul_of_nonneg_left hL2R2 hL.le
      _ ≤ R ^ 3 := hLR3
  field_simp
  have hcore : L * (R ^ 2 + L ^ 2) ≤ 2 * R ^ 3 := by
    nlinarith
  calc
    7 * ell * L * (R ^ 2 + L ^ 2) = (7 * ell) * (L * (R ^ 2 + L ^ 2)) := by ring
    _ ≤ (7 * ell) * (2 * R ^ 3) :=
      mul_le_mul_of_nonneg_left hcore (mul_nonneg (by norm_num) hell)
    _ = ell * R ^ 3 * 14 := by ring

end LiebThirring

end
