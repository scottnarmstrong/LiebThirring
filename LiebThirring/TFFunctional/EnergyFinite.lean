/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy
public import LiebThirring.TFFunctional.TrialDensities

/-! # Order-theoretic finiteness of Thomas--Fermi infima -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

/-- A whole-carrier real lower bound implies finiteness of both the exact and
relaxed Thomas--Fermi infima. The analytic coercivity proof supplies this
helper's lower-bound premise in `Coercivity`. -/
theorem tfEnergies_ne_top_ne_bot_of_lower_bound {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (C : ℝ) (hlower : ∀ ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) →
      -C ≤ tfFunctional a z R ρ) :
    tfEnergy a ν z R ≠ ⊤ ∧ tfEnergy a ν z R ≠ ⊥ ∧
      tfRelaxedEnergy a ν z R ≠ ⊤ ∧ tfRelaxedEnergy a ν z R ≠ ⊥ := by
  obtain ⟨ρ, hρ⟩ := exists_tfDensity_mass ν
  let ρexact : {ρ : TFDensity // tfMass ρ = (ν : ℝ)} := ⟨ρ, hρ⟩
  let ρrelaxed : {ρ : TFDensity // tfMass ρ ≤ (ν : ℝ)} := ⟨ρ, hρ.le⟩
  have hexactTop : tfEnergy a ν z R ≠ ⊤ := by
    apply ne_top_of_le_ne_top (EReal.coe_ne_top (tfFunctional a z R ρ))
    unfold tfEnergy
    exact iInf_le _ ρexact
  have hexactBot : tfEnergy a ν z R ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C))
    unfold tfEnergy
    apply le_iInf
    intro σ
    exact EReal.coe_le_coe_iff.mpr (hlower σ.val σ.property.le)
  have hrelaxedTop : tfRelaxedEnergy a ν z R ≠ ⊤ := by
    apply ne_top_of_le_ne_top (EReal.coe_ne_top (tfFunctional a z R ρ))
    unfold tfRelaxedEnergy
    exact iInf_le _ ρrelaxed
  have hrelaxedBot : tfRelaxedEnergy a ν z R ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C))
    unfold tfRelaxedEnergy
    apply le_iInf
    intro σ
    exact EReal.coe_le_coe_iff.mpr (hlower σ.val σ.property)
  exact ⟨hexactTop, hexactBot, hrelaxedTop, hrelaxedBot⟩

end LiebThirring.TFFunctional

end
