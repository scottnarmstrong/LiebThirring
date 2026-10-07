/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakMultiplier

/-! # Continuity of bounded spatial multiplication on L² -/

public section

open MeasureTheory Filter
open scoped Topology NNReal

namespace LiebThirring.Sobolev

/-- A bounded measurable spatial scalar acts complex linearly on the state carrier. -/
@[expose] noncomputable def boundedSMulLinearMap {N q : ℕ}
    (b : Configuration N → ℂ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (hb : AEStronglyMeasurable b) : State N q →ₗ[ℂ] State N q where
  toFun := fun u => boundedSMul b u B hB hb
  map_add' u v := by
    apply Lp.ext
    filter_upwards [boundedSMul_coeFn b (u + v) B hB hb,
      boundedSMul_coeFn b u B hB hb, boundedSMul_coeFn b v B hB hb,
      Lp.coeFn_add u v,
      Lp.coeFn_add (boundedSMul b u B hB hb) (boundedSMul b v B hB hb)] with x h₀ h₁ h₂ h₃ h₄
    rw [h₀, h₄, Pi.add_apply, h₁, h₂, h₃, Pi.add_apply, smul_add]
  map_smul' c u := by
    change boundedSMul b (c • u) B hB hb = c • boundedSMul b u B hB hb
    apply Lp.ext
    filter_upwards [boundedSMul_coeFn b (c • u) B hB hb,
      boundedSMul_coeFn b u B hB hb, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (boundedSMul b u B hB hb)] with x h₀ h₁ h₂ h₃
    rw [h₀, h₃, Pi.smul_apply, h₁, h₂, Pi.smul_apply]
    exact smul_comm _ _ _

/-- The bounded spatial multiplier is continuous on L². -/
@[expose] noncomputable def boundedSMulCLM {N q : ℕ}
    (b : Configuration N → ℂ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (hb : AEStronglyMeasurable b) : State N q →L[ℂ] State N q :=
  (boundedSMulLinearMap b B hB hb).mkContinuous B
    (fun u => norm_boundedSMul_le b u B hB hb)

/-- Bounded multiplication commutes with L² limits. -/
theorem tendsto_boundedSMul {N q : ℕ} (b : Configuration N → ℂ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (hb : AEStronglyMeasurable b)
    {u : State N q} {v : ℕ → State N q} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun n => boundedSMul b (v n) B hB hb) atTop
      (𝓝 (boundedSMul b u B hB hb)) :=
  ((boundedSMulCLM b B hB hb).continuous.tendsto u).comp hv

end LiebThirring.Sobolev

end
