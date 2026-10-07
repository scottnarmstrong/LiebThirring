/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.MassUpperBound
public import LiebThirring.TFMinimizer.MassLowerBound

/-! # The exact mass of the relaxed TF minimizer

Lieb–Simon (1977) II.17--II.18. The independent upper and slack lower
bounds determine `min(ν,Σz)`, including zero cap and no nuclei.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem tfMass_eq_min_of_relaxed_minimizer {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    tfMass ρ = ((min ν (∑ k, z k) : ℝ≥0) : ℝ) := by
  have hupper := tfMass_le_totalNuclearCharge_of_relaxed_minimizer a ν z hz R hR ρ hmass hmin
  have hZ : ((∑ k, z k : ℝ≥0) : ℝ) = totalNuclearCharge z := by
    simp only [NNReal.coe_sum, totalNuclearCharge]
  rw [NNReal.coe_min, hZ]
  apply le_antisymm (le_min hmass hupper)
  by_cases hfull : tfMass ρ = (ν : ℝ)
  · rw [hfull]
    exact min_le_left _ _
  · have hslack : tfMass ρ < (ν : ℝ) := lt_of_le_of_ne hmass hfull
    exact (min_le_right _ _).trans
      (totalNuclearCharge_le_tfMass_of_mass_lt a ν z R ρ hslack hmin)

end LiebThirring.TFMinimizer

end
