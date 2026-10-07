/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.LpDensity
public import LiebThirring.TFLattice.FloorScaling

/-!
# Normalized filled-cube densities with floor occupations

The local L² error is the sum of the oscillatory error and the rounding error.
Both vanish under Thomas–Fermi scaling. No ordering of a degenerate last shell
is required. Source: Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LiebThirring.TFLattice

theorem volume_physicalCube_eq (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    volume (physicalCube ℓ b) = (cubeCoordinateMeasure ℓ) univ := by
  have he := (measurePreserving_cubeCoordinates_restrict ℓ b).measure_preimage
    MeasurableSet.univ.nullMeasurableSet
  simpa using he

theorem volume_physicalCube_ne_top (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    volume (physicalCube ℓ b) ≠ ∞ := by
  rw [volume_physicalCube_eq]
  exact measure_ne_top _ _

theorem memLp_physicalCube_const (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : ℝ≥0∞) (c : ℝ) :
    MemLp ((physicalCube ℓ b).indicator (fun _ => c)) p volume :=
  memLp_indicator_const p (measurableSet_physicalCube ℓ b) c
    (Or.inr (volume_physicalCube_ne_top ℓ b))

theorem lpNorm_physicalCube_const_two (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (c : ℝ) :
    lpNorm ((physicalCube ℓ b).indicator (fun _ => c)) 2 volume =
      |c| * (ℓ.val ^ 3) ^ (1 / 2 : ℝ) := by
  unfold lpNorm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_physicalCube ℓ b)]
  change lpNorm (fun _ : Position => c) 2 (volume.restrict (physicalCube ℓ b)) = _
  rw [lpNorm_const' (by norm_num) (by simp), Real.norm_eq_abs]
  have hv : (volume.restrict (physicalCube ℓ b)).real univ = ℓ.val ^ 3 := by
    rw [Measure.real, Measure.restrict_apply_univ, volume_physicalCube_eq]
    exact cubeCoordinateMeasure_real_univ ℓ
  rw [hv]
  norm_num

theorem normalized_density_error_decomposition {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q))
    (a m : ℝ) :
    (fun x => physicalFilledDensity ℓ b s x / a -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) =
    a⁻¹ • (fun x => physicalFilledDensity ℓ b s x -
      (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) +
      (physicalCube ℓ b).indicator (fun _ => ((s.card : ℝ) / a - m) / ℓ.val ^ 3) := by
  classical
  ext x
  by_cases hx : x ∈ physicalCube ℓ b
  · simp only [hx, indicator_of_mem, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [div_eq_mul_inv]
    ring
  · simp [physicalFilledDensity, hx]

theorem memLp_normalized_physicalFilledDensity_sub_two {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (s : Finset (ModeIndex q))
    (a m : ℝ) :
    MemLp (fun x => physicalFilledDensity ℓ b s x / a -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) 2 volume := by
  rw [normalized_density_error_decomposition ℓ b s a m]
  exact ((memLp_physicalFilledDensity_sub_two ℓ b s).const_smul a⁻¹).add
    (memLp_physicalCube_const ℓ b 2 _)

theorem lpNorm_normalized_physicalFilledDensity_sub_le {q : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) {a : ℝ} (ha : 0 < a) (m : ℝ) :
    lpNorm (fun x => physicalFilledDensity ℓ b s x / a -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) 2 volume ≤
      Real.sqrt (1944 * q / ℓ.val ^ 3) * (s.card : ℝ) ^ (5 / 6 : ℝ) / a +
      |((s.card : ℝ) / a - m) / ℓ.val ^ 3| * (ℓ.val ^ 3) ^ (1 / 2 : ℝ) := by
  rw [normalized_density_error_decomposition ℓ b s a m]
  calc
    _ ≤ _ := lpNorm_add_le
      ((memLp_physicalFilledDensity_sub_two ℓ b s).const_smul a⁻¹) (by norm_num)
    _ = a⁻¹ * lpNorm (fun x => physicalFilledDensity ℓ b s x -
        (physicalCube ℓ b).indicator (fun _ => (s.card : ℝ) / ℓ.val ^ 3) x) 2 volume +
        |((s.card : ℝ) / a - m) / ℓ.val ^ 3| * (ℓ.val ^ 3) ^ (1 / 2 : ℝ) := by
      rw [lpNorm_const_smul, lpNorm_physicalCube_const_two]
      simp [Real.norm_eq_abs, abs_of_pos ha]
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left
        (lpNorm_physicalFilledDensity_sub_le hq ℓ b hs) (inv_nonneg.mpr ha.le)
      have he' : a⁻¹ * (Real.sqrt (1944 * q / ℓ.val ^ 3) *
          (s.card : ℝ) ^ (5 / 6 : ℝ)) =
          Real.sqrt (1944 * q / ℓ.val ^ 3) * (s.card : ℝ) ^ (5 / 6 : ℝ) / a := by
        ring
      rw [he'] at he
      exact add_le_add_left he _

/-- Filled-density convergence for a translated cube with occupation `floor (a * m)`, including `m = 0`. -/
theorem tendsto_lpNorm_floor_density_two {q : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) {ι : Type*} {l : Filter ι}
    {a : ι → ℝ} (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m)
    (s : ι → Finset (ModeIndex q))
    (hs : ∀ j, IsFilled IsDirichletIndex (s j))
    (hcard : ∀ j, (s j).card = ⌊a j * m⌋₊) :
    Tendsto (fun j => lpNorm (fun x => physicalFilledDensity ℓ b (s j) x / a j -
      (physicalCube ℓ b).indicator (fun _ => m / ℓ.val ^ 3) x) 2 volume) l (𝓝 0) := by
  have hfirst := (tendsto_floor_mass_rpow_div ha hm (by norm_num : (0 : ℝ) ≤ 5 / 6)
    (by norm_num : (5 / 6 : ℝ) < 1)).const_mul (Real.sqrt (1944 * q / ℓ.val ^ 3))
  have hround := (((tendsto_floor_mass_div ha hm).sub_const m).div_const (ℓ.val ^ 3)).abs
  have hlast := hround.mul_const ((ℓ.val ^ 3) ^ (1 / 2 : ℝ))
  have hbound := hfirst.add hlast
  simp only [mul_zero, sub_self, zero_div, abs_zero, zero_mul, add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall fun _ => lpNorm_nonneg) ?_ hbound
  filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
  simpa only [hcard j, mul_div_assoc] using
    lpNorm_normalized_physicalFilledDensity_sub_le hq ℓ b (hs j) hj m

end LiebThirring.TFLattice

end
