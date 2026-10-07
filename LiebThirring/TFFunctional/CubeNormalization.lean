/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CubeDensities
public import LiebThirring.TFFunctional.DensityDifference

/-! # Preserving exact mass in finite cube approximation

Rescaling the literal cell masses preserves a finite regular mesh. Its joint
L1 and L5/3 limit is unchanged when the original masses tend to the target mass.
This supplies the normalization step of the step-density approximation.
-/

public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem tendsto_tfMass_of_tendsto_L1 (f : ℕ → TFDensity) (ρ : TFDensity)
    (hL1 : Tendsto (fun j => ∫ x : Position, |(f j).val x - ρ.val x|)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => tfMass (f j)) atTop (𝓝 (tfMass ρ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hL1
  obtain ⟨J, hJ⟩ := hL1 ε hε
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq]
  apply (abs_tfMass_sub_le (f j) ρ).trans_lt
  simpa only [tfMass_tfDensityAbsDiff, Real.dist_eq, sub_zero,
    abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using hJ j hj

theorem integral_abs_tfDensitySMul_sub_le (b : ℝ≥0) (σ ρ : TFDensity) :
    (∫ x : Position, |(tfDensitySMul b σ).val x - ρ.val x|) ≤
      (b : ℝ) * (∫ x : Position, |σ.val x - ρ.val x|) +
        |(b : ℝ) - 1| * tfMass ρ := by
  have hdiff := ((integrable_tfDensity σ).sub (integrable_tfDensity ρ)).abs
  change Integrable (fun x : Position => |σ.val x - ρ.val x|) volume at hdiff
  have hleft := ((integrable_tfDensity (tfDensitySMul b σ)).sub
    (integrable_tfDensity ρ)).abs
  change Integrable (fun x : Position => |(tfDensitySMul b σ).val x - ρ.val x|)
    volume at hleft
  have hright := (hdiff.const_mul (b : ℝ)).add
    ((integrable_tfDensity ρ).const_mul |(b : ℝ) - 1|)
  calc
    _ ≤ ∫ x : Position, ((b : ℝ) * |σ.val x - ρ.val x| +
        |(b : ℝ) - 1| * ρ.val x) := by
      apply integral_mono_ae hleft hright
      filter_upwards [tfDensitySMul_coeFn b σ, ρ.property.1] with x hx hρ
      change |(tfDensitySMul b σ).val x - ρ.val x| ≤
        (b : ℝ) * |σ.val x - ρ.val x| + |(b : ℝ) - 1| * ρ.val x
      rw [hx]
      calc
        _ = |(b : ℝ) * (σ.val x - ρ.val x) + ((b : ℝ) - 1) * ρ.val x| := by
          congr 1
          ring
        _ ≤ |(b : ℝ) * (σ.val x - ρ.val x)| + |((b : ℝ) - 1) * ρ.val x| :=
          abs_add_le _ _
        _ = _ := by
          exact congrArg₂ (· + ·)
            ((abs_mul _ _).trans (congrArg (· * |σ.val x - ρ.val x|)
              (abs_of_nonneg b.property)))
            ((abs_mul _ _).trans (congrArg (|(b : ℝ) - 1| * ·) (abs_of_nonneg hρ)))
    _ = _ := by
      exact (integral_add (hdiff.const_mul (b : ℝ))
        ((integrable_tfDensity ρ).const_mul |(b : ℝ) - 1|)).trans
        (congrArg₂ (· + ·) (integral_const_mul _ _) (integral_const_mul _ _))

theorem tendsto_tfDensitySMul_joint (f : ℕ → TFDensity) (ρ : TFDensity)
    (b : ℕ → ℝ≥0) (hb : Tendsto (fun j => (b j : ℝ)) atTop (𝓝 1))
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 ρ.val))
    (hL1 : Tendsto (fun j => ∫ x : Position, |(f j).val x - ρ.val x|)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => (tfDensitySMul (b j) (f j)).val) atTop (𝓝 ρ.val) ∧
      Tendsto (fun j => ∫ x : Position, |(tfDensitySMul (b j) (f j)).val x - ρ.val x|)
        atTop (𝓝 (0 : ℝ)) := by
  constructor
  · change Tendsto (fun j => (b j : ℝ) • (f j).val) atTop (𝓝 ρ.val)
    simpa only [one_smul] using hb.smul hLp
  · have hbound : Tendsto (fun j =>
        (b j : ℝ) * (∫ x : Position, |(f j).val x - ρ.val x|) +
          |(b j : ℝ) - 1| * tfMass ρ) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hb.mul hL1).add ((hb.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).abs.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => tfMass ρ) atTop (𝓝 (tfMass ρ))))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => integral_nonneg (fun _ => abs_nonneg _))
      (fun j => integral_abs_tfDensitySMul_sub_le (b j) (f j) ρ)

/-- The literal cell masses multiplied by the ratio of target mass to mesh mass. -/
@[expose] noncomputable def normalizedCubeMesh {B : ℕ} (ν : ℝ≥0)
    (g : TFUpper.CubeMesh B) : TFUpper.CubeMesh B :=
  scaledCubeMesh ⟨(ν : ℝ) / tfMass (tfCubeDensity g),
    div_nonneg ν.property (tfMass_nonneg _)⟩ g

theorem normalizedCubeMesh_represents {B : ℕ} (ν : ℝ≥0) (g : TFUpper.CubeMesh B) :
    (normalizedCubeMesh ν g).represents
      (tfDensitySMul ⟨(ν : ℝ) / tfMass (tfCubeDensity g),
        div_nonneg ν.property (tfMass_nonneg _)⟩ (tfCubeDensity g)) :=
  scaledCubeMesh_represents_tfDensitySMul _ _ _ (cubeMesh_represents_tfCubeDensity g)

theorem tfMass_normalizedCubeDensity {B : ℕ} (ν : ℝ≥0) (g : TFUpper.CubeMesh B)
    (hpos : 0 < tfMass (tfCubeDensity g)) :
    tfMass (tfDensitySMul ⟨(ν : ℝ) / tfMass (tfCubeDensity g),
      div_nonneg ν.property (tfMass_nonneg _)⟩ (tfCubeDensity g)) = (ν : ℝ) := by
  exact (tfMass_tfDensitySMul _ _).trans (div_mul_cancel₀ _ hpos.ne')

end LiebThirring.TFFunctional

end
