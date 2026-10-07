/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.MassFormula
public import LiebThirring.TFMinimizer.Attainment

/-! # TF saturation and exact-mass attainment

The minimizer mass is determined by neutrality and saturation. Source: Lieb–Simon (1977) II.17--II.18. The mass formula for the actual relaxed minimizer,
its proved existence, and exact-equals-relaxed energy give all three clauses.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

/-- Saturation, the exact attainment threshold, and the actual relaxed-minimizer mass. -/
theorem tfEnergy_saturation_and_attainment {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R) :
    tfEnergy a ν z R = tfEnergy a (min ν (∑ k, z k)) z R ∧
      ((∃ ρ : TFDensity, tfMass ρ = (ν : ℝ) ∧
        (tfFunctional a z R ρ : EReal) = tfEnergy a ν z R) ↔ ν ≤ ∑ k, z k) ∧
      (∀ ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) →
        (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R →
          tfMass ρ = ((min ν (∑ k, z k) : ℝ≥0) : ℝ)) := by
  obtain ⟨ρ, hρ, _⟩ := exists_unique_tfRelaxedMinimizer a ν z R
  have hm := tfMass_eq_min_of_relaxed_minimizer a ν z hz R hR ρ hρ.1 hρ.2
  have hF : (tfFunctional a z R ρ : EReal) = tfEnergy a ν z R := by
    rw [tfEnergy_eq_tfRelaxedEnergy_library]
    exact hρ.2
  refine ⟨?_, ?_, tfMass_eq_min_of_relaxed_minimizer a ν z hz R hR⟩
  · apply le_antisymm
    · exact tfEnergy_antitone a z R (min_le_left _ _)
    · exact (tfEnergy_le_trial a (min ν (∑ k, z k)) z R ρ hm).trans hF.le
  · constructor
    · rintro ⟨σ, hσmass, hσF⟩
      have hσmin : (tfFunctional a z R σ : EReal) = tfRelaxedEnergy a ν z R := by
        rwa [tfEnergy_eq_tfRelaxedEnergy_library] at hσF
      have hσ := tfMass_eq_min_of_relaxed_minimizer a ν z hz R hR σ hσmass.le hσmin
      have hreal : (ν : ℝ) ≤ ((∑ k, z k : ℝ≥0) : ℝ) := by
        rw [hσmass] at hσ
        rw [hσ, NNReal.coe_min]
        exact min_le_right _ _
      exact_mod_cast hreal
    · intro hν
      refine ⟨ρ, ?_, hF⟩
      rwa [min_eq_left hν] at hm

end LiebThirring.TFMinimizer

end
