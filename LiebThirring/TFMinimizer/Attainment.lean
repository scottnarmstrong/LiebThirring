/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.MinimizingSequence
public import LiebThirring.TFMinimizer.MassClosed
public import LiebThirring.TFMinimizer.Continuity

/-! # Unique relaxed Thomas--Fermi minimizer

A relaxed minimizer exists and is unique. The strong-Cauchy adaptation uses completeness, Fatou for mass, and
the proved adjustable-radius interaction estimates.
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

/-- Relaxed attainment holds at every mass cap; no chosen minimizer is defined. -/
theorem exists_unique_tfRelaxedMinimizer {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∃! ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) ∧
      (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R := by
  obtain ⟨f, hcap, hupper, hF⟩ := exists_tfRelaxed_minimizing_sequence a ν z R
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_tfFunctional_le a ν z R
    ((tfRelaxedEnergy a ν z R).toReal + 1)
  have hC := cauchySeq_of_tfRelaxed_minimizing a ν z R f hcap hF B hB
    (fun j => hbound (f j) (hcap j) (hupper j))
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨ρ, hρ, hmass⟩ := exists_tfDensity_of_tendsto_mass_le ν f hcap g hg
  have hLp : Tendsto (fun j => (f j).val) atTop (𝓝 ρ.val) := by rwa [hρ]
  have hval : tfFunctional a z R ρ = (tfRelaxedEnergy a ν z R).toReal :=
    tendsto_nhds_unique
      (tendsto_tfFunctional_of_tendsto_mass_le a z R ν f ρ hcap hmass hLp) hF
  have hf := tfEnergy_ne_top_ne_bot_library a ν z R
  have hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R := by
    rw [hval, EReal.coe_toReal hf.2.2.1 hf.2.2.2]
  refine ⟨ρ, ⟨hmass, hmin⟩, ?_⟩
  intro σ hσ
  by_contra hne
  have hstrict := tfFunctional_tfMidpoint_lt a z R σ ρ hne
  have hmid : tfMass (tfMidpoint σ ρ) ≤ (ν : ℝ) := by
    rw [tfMass_tfMidpoint]
    linarith [hσ.1]
  have hlo := tfRelaxedEnergy_toReal_le_trial a ν z R _ hmid
  have hσval : tfFunctional a z R σ = (tfRelaxedEnergy a ν z R).toReal := by
    have h := congrArg EReal.toReal hσ.2
    simpa only [EReal.toReal_coe] using h
  linarith

end LiebThirring.TFMinimizer

end
