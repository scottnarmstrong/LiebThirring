/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.AttractionCoercivity
public import LiebThirring.TFFunctional.Variational

/-! # Actual almost minimizing TF densities

The finite literal infimum supplies exact-mass trials; no minimizer attainment
is assumed. Proof: kinetic coercivity–coefficient continuity.
-/

public section

open MeasureTheory
open scoped NNReal ENNReal
namespace LiebThirring.TFFunctional

theorem exists_tfDensity_near_tfEnergy {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : TFDensity, tfMass ρ = (ν : ℝ) ∧
      tfFunctional a z R ρ < (tfEnergy a ν z R).toReal + ε := by
  have hf := tfEnergy_ne_top_ne_bot_library a ν z R
  have hlt : tfEnergy a ν z R <
      (((tfEnergy a ν z R).toReal + ε : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hf.1 hf.2.1]
    apply EReal.coe_lt_coe_iff.mpr
    simpa only [EReal.toReal_coe] using lt_add_of_pos_right
      (tfEnergy a ν z R).toReal hε
  unfold tfEnergy at hlt
  obtain ⟨ρ, hρ⟩ := iInf_lt_iff.mp hlt
  exact ⟨ρ.val, ρ.property, EReal.coe_lt_coe_iff.mp hρ⟩

theorem tfEnergy_toReal_le_trial {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hmass : tfMass ρ = (ν : ℝ)) :
    (tfEnergy a ν z R).toReal ≤ tfFunctional a z R ρ := by
  have hf := tfEnergy_ne_top_ne_bot_library a ν z R
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hf.1 hf.2.1]
  exact tfEnergy_le_trial a ν z R ρ hmass

end LiebThirring.TFFunctional

end
