/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Continuity

/-! # Continuity of the full Thomas--Fermi functional -/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem tendsto_tfFunctional {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val))
    (hL1 : Tendsto (fun j => ∫ x : Position, |(f j).val x - σ.val x|)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => tfFunctional a z R (f j)) atTop (𝓝 (tfFunctional a z R σ)) := by
  have hnorm : Tendsto (fun j => ‖(f j).val‖) atTop (𝓝 ‖σ.val‖) := hLp.norm
  have hkin : Tendsto (fun j => ∫ x : Position, ((f j).val x) ^ ((5 : ℝ) / 3))
      atTop (𝓝 (∫ x : Position, (σ.val x) ^ ((5 : ℝ) / 3))) := by
    simp_rw [integral_tfDensity_rpow_eq_norm]
    exact hnorm.rpow_const (by norm_num)
  unfold tfFunctional
  exact (tendsto_const_nhds.mul hkin).sub
    (tendsto_integral_tfNuclearPotential_mul z R f σ hLp hL1) |>.add
      (tendsto_tfCoulombEnergy_self f σ hLp hL1)

end LiebThirring.TFFunctional

end
