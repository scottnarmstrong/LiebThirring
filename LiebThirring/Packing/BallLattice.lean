/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.BallShells
public import LiebThirring.Packing.InteriorLattice

/-!
# Lattice counts in balls and annuli

Boundary-error estimates, assembled from the actual eligible lattice cubes.
-/

public section

open MeasureTheory Metric Set

namespace LiebThirring

open Filter Topology

/-- The actual number of side-`ℓ` lattice cubes whose interiors lie in `B(0,L)`. -/
@[expose] noncomputable def ballLatticeCount (ell L : ℝ) (hell : 0 < ell) : ℕ :=
  (interiorLatticeCubes ell (ball (0 : Position) L) hell isBounded_ball).card

/-- The actual number of side-`ℓ` lattice cubes whose interiors lie in
`B(0,R) \ closedBall(0,L)`. -/
@[expose] noncomputable def annulusLatticeCount (ell L R : ℝ) (hell : 0 < ell) : ℕ :=
  (interiorLatticeCubes ell (openAnnulus (0 : Position) L R) hell
    (isBounded_ball.subset sdiff_subset)).card

theorem volume_real_openAnnulus (c : Position) {L R : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R) :
    volume.real (openAnnulus c L R) = ballVolumeConstant * (R ^ 3 - L ^ 3) := by
  rcases hLR.eq_or_lt with rfl | hLR
  · have hempty : openAnnulus c L L = ∅ := by
      exact sdiff_eq_empty.mpr ball_subset_closedBall
    rw [hempty]
    simp
  · rw [openAnnulus, measureReal_sdiff (closedBall_subset_ball hLR)
      measurableSet_closedBall]
    rw [volume_real_ball_position _ (hL.trans hLR.le), volume_real_closedBall_position _ hL]
    ring

/-- The inner-ball lattice deficit is nonnegative. -/
theorem ballLatticeCount_deficit_nonneg {ell L : ℝ} (hell : 0 < ell) (hL : 0 ≤ L) :
    0 ≤ ballVolumeConstant * L ^ 3 - ballLatticeCount ell L hell * ell ^ 3 := by
  simpa [ballLatticeCount, volume_real_ball_position (0 : Position) hL] using
    interior_lattice_volume_deficit_nonneg hell (Metric.isBounded_ball (x := (0 : Position)) (r := L))

/-- The inner-ball lattice deficit is controlled by its spherical boundary layer. -/
theorem ballLatticeCount_deficit_le {ell L : ℝ} (hell : 0 < ell)
    (hdiam : Real.sqrt 3 * ell ≤ L) :
    ballVolumeConstant * L ^ 3 - ballLatticeCount ell L hell * ell ^ 3 ≤
      3 * ballVolumeConstant * L ^ 2 * (Real.sqrt 3 * ell) := by
  have hL : 0 ≤ L := le_trans (mul_nonneg (Real.sqrt_nonneg 3) hell.le) hdiam
  calc
    ballVolumeConstant * L ^ 3 - ballLatticeCount ell L hell * ell ^ 3 =
        volume.real (ball (0 : Position) L) -
          ballLatticeCount ell L hell * ell ^ 3 := by rw [volume_real_ball_position _ hL]
    _ ≤ volume.real (latticeBoundaryLayer ell (ball (0 : Position) L)) := by
      simpa [ballLatticeCount] using interior_lattice_volume_deficit_le_boundaryLayer hell
        (Metric.isBounded_ball (x := (0 : Position)) (r := L))
    _ ≤ volume.real
        (ball (0 : Position) L \ ball 0 (L - Real.sqrt 3 * ell)) := by
      exact measureReal_mono (latticeBoundaryLayer_ball_subset (0 : Position)) (by
        exact measure_ne_top_of_subset sdiff_subset (by rw [volume_ball_position]; finiteness))
    _ ≤ 3 * ballVolumeConstant * L ^ 2 * (Real.sqrt 3 * ell) :=
      volume_ball_diff_ball_le (0 : Position) hL
        (mul_nonneg (Real.sqrt_nonneg 3) hell.le) hdiam

/-- The occupied fraction of an eligible ball lattice is at most one. -/
theorem ballLatticeCount_normalized_le_one {ell L : ℝ} (hell : 0 < ell) (hL : 0 < L) :
    ballLatticeCount ell L hell * ell ^ 3 / (ballVolumeConstant * L ^ 3) ≤ 1 := by
  apply (div_le_one (mul_pos ballVolumeConstant_pos (pow_pos hL _))).mpr
  exact sub_nonneg.mp (ballLatticeCount_deficit_nonneg hell hL.le)

/-- Quantitative convergence of the occupied ball-lattice fraction. -/
theorem one_sub_ballLatticeCount_normalized_le {ell L : ℝ} (hell : 0 < ell)
    (hdiam : Real.sqrt 3 * ell ≤ L) :
    1 - ballLatticeCount ell L hell * ell ^ 3 / (ballVolumeConstant * L ^ 3) ≤
      3 * Real.sqrt 3 * ell / L := by
  have hL : 0 < L := lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 (by norm_num)) hell) hdiam
  have hden : 0 < ballVolumeConstant * L ^ 3 :=
    mul_pos ballVolumeConstant_pos (pow_pos hL _)
  rw [← div_self hden.ne', ← sub_div]
  apply (div_le_iff₀ hden).2
  have hb := ballLatticeCount_deficit_le hell hdiam
  calc
    ballVolumeConstant * L ^ 3 - ballLatticeCount ell L hell * ell ^ 3 ≤
        3 * ballVolumeConstant * L ^ 2 * (Real.sqrt 3 * ell) := hb
    _ = (3 * Real.sqrt 3 * ell / L) * (ballVolumeConstant * L ^ 3) := by
      field_simp

/-- For fixed lattice side, eligible cubes fill asymptotically all of a growing ball. -/
theorem tendsto_ballLatticeCount_normalized (ell : ℝ) (hell : 0 < ell) :
    Tendsto (fun L : ℝ =>
      ballLatticeCount ell L hell * ell ^ 3 / (ballVolumeConstant * L ^ 3))
      atTop (nhds 1) := by
  have hupper : Tendsto (fun _L : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have herror : Tendsto (fun L : ℝ => 3 * Real.sqrt 3 * ell / L) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id _
  have hlower : Tendsto (fun L : ℝ => 1 - 3 * Real.sqrt 3 * ell / L) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop (Real.sqrt 3 * ell)] with L hL
    have := one_sub_ballLatticeCount_normalized_le hell hL
    linarith
  · filter_upwards [eventually_gt_atTop 0] with L hL
    exact ballLatticeCount_normalized_le_one hell hL

/-- The annulus lattice deficit is nonnegative. -/
theorem annulusLatticeCount_deficit_nonneg {ell L R : ℝ} (hell : 0 < ell)
    (hL : 0 ≤ L) (hLR : L ≤ R) :
    0 ≤ ballVolumeConstant * (R ^ 3 - L ^ 3) -
      annulusLatticeCount ell L R hell * ell ^ 3 := by
  have hvol := volume_real_openAnnulus (0 : Position) hL hLR
  rw [← hvol]
  unfold annulusLatticeCount
  exact interior_lattice_volume_deficit_nonneg hell (Metric.isBounded_ball.subset sdiff_subset)

/-- The explicit annular lattice deficit, with `C = 7 √3 σ`. -/
theorem annulusLatticeCount_deficit_le {ell L R : ℝ} (hell : 0 < ell)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hdiam : Real.sqrt 3 * ell ≤ L) :
    ballVolumeConstant * (R ^ 3 - L ^ 3) -
        annulusLatticeCount ell L R hell * ell ^ 3 ≤
      7 * Real.sqrt 3 * ballVolumeConstant * ell * (R ^ 2 + L ^ 2) := by
  have hR : 0 ≤ R := hL.trans hLR
  have hvol := volume_real_openAnnulus (0 : Position) hL hLR
  calc
    ballVolumeConstant * (R ^ 3 - L ^ 3) -
        annulusLatticeCount ell L R hell * ell ^ 3 =
        volume.real (openAnnulus (0 : Position) L R) -
          annulusLatticeCount ell L R hell * ell ^ 3 := by rw [hvol]
    _ ≤ volume.real (latticeBoundaryLayer ell (openAnnulus (0 : Position) L R)) := by
      unfold annulusLatticeCount
      exact interior_lattice_volume_deficit_le_boundaryLayer hell
        (Metric.isBounded_ball.subset sdiff_subset)
    _ ≤ volume.real ((ball (0 : Position) R \ ball 0 (R - Real.sqrt 3 * ell)) ∪
        (closedBall 0 (L + Real.sqrt 3 * ell) \ closedBall 0 L)) := by
      refine measureReal_mono (latticeBoundaryLayer_openAnnulus_subset_shells (0 : Position)) ?_
      have hsub :
          (ball (0 : Position) R \ ball 0 (R - Real.sqrt 3 * ell)) ∪
              (closedBall 0 (L + Real.sqrt 3 * ell) \ closedBall 0 L) ⊆
            closedBall 0 (R + Real.sqrt 3 * ell) := by
        apply union_subset
        · exact sdiff_subset.trans (ball_subset_closedBall.trans
            (closedBall_subset_closedBall (le_add_of_nonneg_right
              (mul_nonneg (Real.sqrt_nonneg 3) hell.le))))
        · exact sdiff_subset.trans (closedBall_subset_closedBall (by linarith))
      exact measure_ne_top_of_subset hsub (by rw [volume_closedBall_position]; finiteness)
    _ ≤ 7 * Real.sqrt 3 * ballVolumeConstant * ell * (R ^ 2 + L ^ 2) :=
      volume_real_annulus_lattice_shells_le (0 : Position) hL hLR hell.le hdiam

/-- The normalized annular deficit is at most `14 √3 ℓ/L`. -/
theorem annulusLatticeCount_deficit_normalized_le {ell L R : ℝ} (hell : 0 < ell)
    (hL : 0 < L) (hLR : L ≤ R) (hdiam : Real.sqrt 3 * ell ≤ L) :
    (ballVolumeConstant * (R ^ 3 - L ^ 3) -
        annulusLatticeCount ell L R hell * ell ^ 3) /
        (ballVolumeConstant * R ^ 3) ≤
      14 * Real.sqrt 3 * ell / L := by
  calc
    (ballVolumeConstant * (R ^ 3 - L ^ 3) -
        annulusLatticeCount ell L R hell * ell ^ 3) /
        (ballVolumeConstant * R ^ 3) ≤
      (7 * Real.sqrt 3 * ballVolumeConstant * ell * (R ^ 2 + L ^ 2)) /
        (ballVolumeConstant * R ^ 3) :=
      div_le_div_of_nonneg_right
        (annulusLatticeCount_deficit_le hell hL.le hLR hdiam)
        (mul_nonneg ballVolumeConstant_pos.le (pow_nonneg (hL.trans_le hLR).le _))
    _ ≤ 14 * Real.sqrt 3 * ell / L :=
      annulus_lattice_shell_normalized_le hL hLR hell.le

/-- Along any growing inner radii and enclosing outer radii, the normalized annular
lattice residual tends to zero. The estimate is uniform in the outer radius. -/
theorem tendsto_annulusLatticeCount_deficit_normalized {J : Type*} {l : Filter J}
    (ell : ℝ) (hell : 0 < ell) (L R : J → ℝ) (hL : Tendsto L l atTop)
    (hLR : ∀ᶠ j in l, L j ≤ R j) :
    Tendsto (fun j =>
      (ballVolumeConstant * (R j ^ 3 - L j ^ 3) -
          annulusLatticeCount ell (L j) (R j) hell * ell ^ 3) /
        (ballVolumeConstant * R j ^ 3)) l (nhds 0) := by
  have herr : Tendsto (fun j => 14 * Real.sqrt 3 * ell / L j) l (nhds 0) :=
    Filter.Tendsto.const_div_atTop hL _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
  · filter_upwards [hL.eventually (eventually_gt_atTop 0), hLR] with j hLj hLRj
    exact div_nonneg (annulusLatticeCount_deficit_nonneg hell hLj.le hLRj)
      (mul_nonneg ballVolumeConstant_pos.le (pow_nonneg (hLj.trans_le hLRj).le _))
  · filter_upwards [hL.eventually (eventually_ge_atTop (Real.sqrt 3 * ell)), hLR]
      with j hdiam hLRj
    exact annulusLatticeCount_deficit_normalized_le hell
      (lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 (by norm_num)) hell) hdiam) hLRj hdiam

end LiebThirring

end
