/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.CubeStep
public import LiebThirring.TFFunctional.TrialDensities
public import LiebThirring.TFFunctional.Operations

/-! # Finite regular cube densities on the TF carrier

The mesh has the literal half-open lattice cells used by the upper-bound
consumer. These constructions implement the finite-step part of step-density approximation.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem cubeMesh_stepFunction_nonneg {B : ℕ} (g : TFUpper.CubeMesh B) (x : Position) :
    0 ≤ g.stepFunction x := by
  apply Finset.sum_nonneg
  intro b _
  exact indicator_nonneg (fun _ _ => div_nonneg (g.mass b).property
    (pow_nonneg g.side.property.le 3)) x

theorem memLp_cubeMesh_stepFunction {B : ℕ} (g : TFUpper.CubeMesh B) :
    MemLp g.stepFunction ((5 : ℝ≥0∞) / 3) volume := by
  apply memLp_finsetSum
  intro b _
  apply memLp_indicator_const _ (measurableSet_latticeCell _ _) _
  right
  rw [volume_latticeCell g.side.property.le]
  exact ENNReal.ofReal_ne_top

/-- The literal finite cube formula packaged in the density carrier. -/
@[expose] noncomputable def tfCubeDensity {B : ℕ} (g : TFUpper.CubeMesh B) : TFDensity :=
  tfDensityOfFunction g.stepFunction (memLp_cubeMesh_stepFunction g)
    (Filter.Eventually.of_forall (cubeMesh_stepFunction_nonneg g))
    g.integrable_stepFunction

theorem cubeMesh_represents_tfCubeDensity {B : ℕ} (g : TFUpper.CubeMesh B) :
    g.represents (tfCubeDensity g) := tfDensityOfFunction_coeFn _ _ _ _

/-- Multiplying every cell mass preserves the regular mesh. -/
@[expose] def scaledCubeMesh {B : ℕ} (b : ℝ≥0) (g : TFUpper.CubeMesh B) :
    TFUpper.CubeMesh B where
  side := g.side
  label := g.label
  distinct := g.distinct
  mass i := b * g.mass i

theorem scaledCubeMesh_stepFunction {B : ℕ} (b : ℝ≥0) (g : TFUpper.CubeMesh B)
    (x : Position) : (scaledCubeMesh b g).stepFunction x = (b : ℝ) * g.stepFunction x := by
  unfold TFUpper.CubeMesh.stepFunction scaledCubeMesh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ latticeCell g.side.val (g.label i)
  · simp only [indicator_of_mem hx, NNReal.coe_mul]
    ring
  · simp only [indicator_of_notMem hx, mul_zero]

theorem scaledCubeMesh_represents_tfDensitySMul {B : ℕ} (b : ℝ≥0)
    (g : TFUpper.CubeMesh B) (ρ : TFDensity) (hρ : g.represents ρ) :
    (scaledCubeMesh b g).represents (tfDensitySMul b ρ) := by
  filter_upwards [tfDensitySMul_coeFn b ρ, hρ] with x hx hg
  rw [hx, hg, scaledCubeMesh_stepFunction]

end LiebThirring.TFFunctional

end
