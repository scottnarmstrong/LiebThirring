/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.EigenvalueEstimate
public import LiebThirring.TFLattice.FloorPowers

/-!
# Scaled kinetic energy of floor occupations

The sharp first-n bound and floor convergence yield the exact semiclassical
kinetic limit needed by finite-cube upper trials. Source: Lieb–Simon (1977) III.13–14,
pp. 67–71 (sharp eigenvalue sums/filled-density convergence).
-/

public section

open Filter Topology

namespace LiebThirring.TFLattice

/-- The floor kinetic limit, valid for every choice within the last shell. -/
theorem tendsto_floor_dirichlet_cubeKinetic {q : ℕ} (hq : 1 ≤ q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l atTop) {m : ℝ} (hm : 0 ≤ m)
    (s : ι → Finset (ModeIndex q)) (hs : ∀ j, IsFilled IsDirichletIndex (s j))
    (hcard : ∀ j, (s j).card = ⌊a j * m⌋₊) :
    Tendsto (fun j => (∑ p ∈ s j, cubeEigenvalue ℓ p) / (a j) ^ (5 / 3 : ℝ)) l
      (𝓝 ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * m ^ (5 / 3 : ℝ))) := by
  have hmain := (tendsto_const_nhds : Tendsto
    (fun _ : ι => (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2) l
      (𝓝 ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2))).mul
    (tendsto_floor_mass_rpow_ratio ha hm (by norm_num : (0 : ℝ) ≤ 5 / 3))
  have herr := (tendsto_const_nhds : Tendsto
    (fun _ : ι => cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2) l
      (𝓝 (cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2))).mul
    (tendsto_floor_mass_rpow_ratio_zero ha hm (by norm_num : (0 : ℝ) ≤ 4 / 3)
      (by norm_num : (4 / 3 : ℝ) < 5 / 3))
  have hl : Tendsto (fun j =>
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 *
        ((⌊a j * m⌋₊ : ℝ) ^ (5 / 3 : ℝ) / (a j) ^ (5 / 3 : ℝ)) -
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 *
        ((⌊a j * m⌋₊ : ℝ) ^ (4 / 3 : ℝ) / (a j) ^ (5 / 3 : ℝ))) l
        (𝓝 ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * m ^ (5 / 3 : ℝ))) := by
    simpa only [mul_zero, sub_zero] using hmain.sub herr
  have hu : Tendsto (fun j =>
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 *
        ((⌊a j * m⌋₊ : ℝ) ^ (5 / 3 : ℝ) / (a j) ^ (5 / 3 : ℝ)) +
      cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 *
        ((⌊a j * m⌋₊ : ℝ) ^ (4 / 3 : ℝ) / (a j) ^ (5 / 3 : ℝ))) l
        (𝓝 ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * m ^ (5 / 3 : ℝ))) := by
    simpa only [mul_zero, add_zero] using hmain.add herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
    have hb := (abs_le.mp (sum_cubeEigenvalue_dirichlet_error_le hq ℓ (hs j))).1
    rw [hcard j] at hb
    have hlow : (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 *
        (⌊a j * m⌋₊ : ℝ) ^ (5 / 3 : ℝ) -
        cubeEigenvalueErrorConstant q * ℓ.val⁻¹ ^ 2 * (⌊a j * m⌋₊ : ℝ) ^ (4 / 3 : ℝ) ≤
        ∑ p ∈ s j, cubeEigenvalue ℓ p := by linarith only [hb]
    have hd := div_le_div_of_nonneg_right hlow (Real.rpow_pos_of_pos hj (5 / 3 : ℝ)).le
    simpa only [sub_div, mul_div_assoc] using hd
  · filter_upwards [ha.eventually (eventually_gt_atTop 0)] with j hj
    have hb := sum_cubeEigenvalue_dirichlet_upper hq ℓ (hs j)
    rw [hcard j] at hb
    have hd := div_le_div_of_nonneg_right hb (Real.rpow_pos_of_pos hj (5 / 3 : ℝ)).le
    simpa only [add_div, mul_div_assoc] using hd

end LiebThirring.TFLattice

end
