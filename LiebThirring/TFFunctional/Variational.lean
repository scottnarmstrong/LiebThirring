/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy

/-! # Order properties of the literal TF variational infima

Exact and relaxed competitors are kept separate. The mass-completion helper
isolates the order argument from the diffuse-density construction of mass completion.
-/

public section

open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem tfEnergy_le_trial {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hρ : tfMass ρ = (ν : ℝ)) :
    tfEnergy a ν z R ≤ (tfFunctional a z R ρ : EReal) := by
  unfold tfEnergy
  exact iInf_le _ (⟨ρ, hρ⟩ : {ρ : TFDensity // tfMass ρ = (ν : ℝ)})

theorem tfRelaxedEnergy_le_trial {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hρ : tfMass ρ ≤ (ν : ℝ)) :
    tfRelaxedEnergy a ν z R ≤ (tfFunctional a z R ρ : EReal) := by
  unfold tfRelaxedEnergy
  exact iInf_le _ (⟨ρ, hρ⟩ : {ρ : TFDensity // tfMass ρ ≤ (ν : ℝ)})

theorem tfRelaxedEnergy_le_tfEnergy {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfRelaxedEnergy a ν z R ≤ tfEnergy a ν z R := by
  unfold tfEnergy
  apply le_iInf
  intro ρ
  exact tfRelaxedEnergy_le_trial a ν z R ρ.val ρ.property.le

theorem tfRelaxedEnergy_antitone {M : ℕ} (a : {a : ℝ // 0 < a})
    {ν ν' : ℝ≥0} (hν : ν ≤ ν') (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfRelaxedEnergy a ν' z R ≤ tfRelaxedEnergy a ν z R := by
  unfold tfRelaxedEnergy
  apply le_iInf
  intro ρ
  exact iInf_le_of_le ⟨ρ.val, ρ.property.trans (by exact_mod_cast hν)⟩ le_rfl

/-- Order-theoretic reduction of exact/relaxed equality to actual mass completion
with arbitrarily small added energy. This helper has an explicit analytic premise. -/
theorem tfEnergy_eq_tfRelaxedEnergy_of_mass_completion {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hcomplete : ∀ ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) → ∀ ε : ℝ, 0 < ε →
      ∃ σ : TFDensity, tfMass σ = (ν : ℝ) ∧
        tfFunctional a z R σ ≤ tfFunctional a z R ρ + ε) :
    tfEnergy a ν z R = tfRelaxedEnergy a ν z R := by
  apply le_antisymm _ (tfRelaxedEnergy_le_tfEnergy a ν z R)
  unfold tfRelaxedEnergy
  apply le_iInf
  intro ρ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro b hb
  have hε : 0 < b - tfFunctional a z R ρ.val :=
    sub_pos.mpr (EReal.coe_lt_coe_iff.mp hb)
  obtain ⟨σ, hσ, hE⟩ := hcomplete ρ.val ρ.property _ hε
  apply (tfEnergy_le_trial a ν z R σ hσ).trans
  apply EReal.coe_le_coe_iff.mpr
  linarith

end LiebThirring.TFFunctional

end
