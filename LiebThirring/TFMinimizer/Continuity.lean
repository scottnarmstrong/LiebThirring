/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.PotentialEstimates

/-! # Strong L5/3 continuity at bounded mass

First make the far-field error small, then the norm error.
This does not require convergence of mass or L1 convergence.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- An adjustable inverse-radius error may be removed before taking the limit. -/
theorem tendsto_of_dist_le_mul_add_inv (f d : ℕ → ℝ) (c b : ℝ) (hb : 0 ≤ b)
    (A : ℝ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hbound : ∀ r : ℝ, 0 < r → ∀ j, dist (f j) c ≤ A r * d j + b / r) :
    Tendsto f atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let r := (2 * b + 1) / ε
  have hr : 0 < r := div_pos (by linarith) hε
  have hre : r * ε = 2 * b + 1 := div_mul_cancel₀ _ hε.ne'
  have htail : b / r < ε / 2 := by
    apply (div_lt_iff₀ hr).mpr
    nlinarith only [hre]
  have hsmall : ∀ᶠ j in atTop, A r * d j < ε / 2 := by
    have h : Tendsto (fun j => A r * d j) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hd
    exact h.eventually (eventually_lt_nhds (half_pos hε))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hsmall
  refine ⟨J, fun j hj => ?_⟩
  exact (hbound r hr j).trans_lt (by linarith [hJ j hj])

theorem tendsto_attraction_of_tendsto_mass_le {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ν : ℝ≥0)
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ)) (hσ : tfMass σ ≤ (ν : ℝ))
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val)) :
    Tendsto (fun j => ∫ x : Position, tfNuclearPotential z R x * (f j).val x)
      atTop (𝓝 (∫ x : Position, tfNuclearPotential z R x * σ.val x)) := by
  have hn : Tendsto (fun j => ‖(f j).val - σ.val‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hLp.sub_const σ.val).norm
  apply tendsto_of_dist_le_mul_add_inv _ _ _ (2 * (ν : ℝ) * totalNuclearCharge z)
    (by positivity [totalNuclearCharge_nonneg z])
    (fun r => totalNuclearCharge z * (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5)) hn
  intro r hr j
  rw [Real.dist_eq]
  apply (abs_attraction_sub_le_radius z R (f j) σ r hr).trans
  have hm : tfMass (f j) + tfMass σ ≤ 2 * (ν : ℝ) := by linarith [hcap j]
  have ht := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm hr.le)
    (totalNuclearCharge_nonneg z)
  convert add_le_add_right ht
    (totalNuclearCharge z * (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) *
      ‖(f j).val - σ.val‖) using 1 <;> ring

theorem tendsto_coulomb_self_of_tendsto_mass_le (ν : ℝ≥0)
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ)) (hσ : tfMass σ ≤ (ν : ℝ))
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val)) :
    Tendsto (fun j => tfCoulombEnergy (f j) (f j)) atTop (𝓝 (tfCoulombEnergy σ σ)) := by
  have hn : Tendsto (fun j => ‖(f j).val - σ.val‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hLp.sub_const σ.val).norm
  apply tendsto_of_dist_le_mul_add_inv _ _ _ (8 * (ν : ℝ) ^ 2) (by positivity)
    (fun r => 4 * (ν : ℝ) * (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5)) hn
  intro r hr j
  rw [Real.dist_eq]
  apply (abs_coulomb_self_sub_le_radius (f j) σ r hr).trans
  have hm : tfMass (f j) + tfMass σ ≤ 2 * (ν : ℝ) := by linarith [hcap j]
  have hn0 := norm_nonneg ((f j).val - σ.val)
  have hC : 0 ≤ (8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) :=
    Real.rpow_nonneg (by positivity) _
  have hm0 := add_nonneg (tfMass_nonneg (f j)) (tfMass_nonneg σ)
  have ht := div_le_div_of_nonneg_right hm hr.le
  have hmul := mul_le_mul (by linarith : 2 * (tfMass (f j) + tfMass σ) ≤ 4 * (ν : ℝ))
    (add_le_add_right ht ((8 * Real.pi * Real.sqrt r) ^ ((2 : ℝ) / 5) * ‖(f j).val - σ.val‖))
    (add_nonneg (mul_nonneg hC hn0) (div_nonneg hm0 hr.le)) (by positivity : 0 ≤ 4 * (ν : ℝ))
  convert hmul using 1
  ring

/-- All three literal terms are continuous along a strong-Lp sequence with a
uniform mass cap, including when mass escapes to infinity. -/
theorem tendsto_tfFunctional_of_tendsto_mass_le {M : ℕ}
    (a : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ν : ℝ≥0)
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ)) (hσ : tfMass σ ≤ (ν : ℝ))
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val)) :
    Tendsto (fun j => tfFunctional a z R (f j)) atTop (𝓝 (tfFunctional a z R σ)) := by
  have hk : Tendsto (fun j => ∫ x : Position, ((f j).val x) ^ ((5 : ℝ) / 3))
      atTop (𝓝 (∫ x : Position, (σ.val x) ^ ((5 : ℝ) / 3))) := by
    simp_rw [integral_tfDensity_rpow_eq_norm]
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 3)).continuousAt.tendsto.comp hLp.norm
  exact ((tendsto_const_nhds.mul hk).sub
    (tendsto_attraction_of_tendsto_mass_le z R ν f σ hcap hσ hLp)).add
      (tendsto_coulomb_self_of_tendsto_mass_le ν f σ hcap hσ hLp)

end LiebThirring.TFMinimizer

end
