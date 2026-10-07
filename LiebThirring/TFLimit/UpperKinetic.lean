/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.Occupation
public import LiebThirring.TFUpper.CubeStep
public import LiebThirring.TFLimit.ElectronicLimit
import LiebThirring.TFLattice.KineticScaling

/-! # The occupied-cube kinetic limit for the upper assembly

The proved sharp eigenvalue sums floor Dirichlet limit is summed over the finite mesh. This
produces the exact kinetic-limit input for the Dirichlet orbitals with no external kinetic hypothesis.
Source: Lieb–Simon (1977) III.13--14, pp. 67--71.
-/

public section
open Filter
open scoped NNReal Topology
namespace LiebThirring.TFLimit
open TFUpper

/-- The exact sharp eigenvalue sums input for Dirichlet orbital estimates, including zero-mass cells and empty meshes. -/
theorem tendsto_scaled_occupiedCubeKinetic
    (q : {q : ℕ // 1 ≤ q}) (ν : ℝ≥0) (hν : 0 < ν)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) {B : ℕ} (g : CubeMesh B) :
    Tendsto (fun j => (((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(5 : ℝ) / 3) *
      occupiedCubeKinetic q.val (show 0 < q.val from q.property) g.side
        ((N j : ℝ≥0) / ν) g.mass) atTop
      (𝓝 ((tfKineticConstant q).val *
        (g.side.val⁻¹ ^ 2 * ∑ b, (g.mass b : ℝ) ^ ((5 : ℝ) / 3)))) := by
  let α : ℕ → ℝ≥0 := fun j => (N j : ℝ≥0) / ν
  have hα : Tendsto (fun j => (α j : ℝ)) atTop atTop :=
    tendsto_largeCharge_parameter ν hν N hN
  have hpow (a : ℝ≥0) :
      (a : ℝ) ^ (-(5 : ℝ) / 3) = ((a : ℝ) ^ ((5 : ℝ) / 3))⁻¹ := by
    rw [neg_div]
    exact Real.rpow_neg a.property ((5 : ℝ) / 3)
  have hb (b : Fin B) :
      Tendsto (fun j => (α j : ℝ) ^ (-(5 : ℝ) / 3) *
        ∑ p ∈ filledDirichletModes q.val (show 0 < q.val from q.property)
          (cubeOccupation (α j) (g.mass b)), TFLattice.cubeEigenvalue g.side p)
        atTop (𝓝 ((tfKineticConstant q).val * g.side.val⁻¹ ^ 2 *
          (g.mass b : ℝ) ^ ((5 : ℝ) / 3))) := by
    have h := TFLattice.tendsto_floor_dirichlet_cubeKinetic q.property
      g.side hα (g.mass b).property
      (fun j => filledDirichletModes q.val (show 0 < q.val from q.property)
        (cubeOccupation (α j) (g.mass b)))
      (fun j => isFilled_filledDirichletModes _ _ _)
      (fun j => card_filledDirichletModes _ _ _)
    apply h.congr'
    exact Filter.Eventually.of_forall (fun j => by
      dsimp only
      rw [hpow (α j), div_eq_mul_inv, mul_comm])
  have hsum := tendsto_finsetSum Finset.univ (fun b _ => hb b)
  simpa only [occupiedCubeKinetic, ← Finset.mul_sum, mul_assoc] using hsum

end LiebThirring.TFLimit
end
