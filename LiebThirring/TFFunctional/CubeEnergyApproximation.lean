/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CubeApproximation
public import LiebThirring.TFFunctional.FunctionalContinuity
public import LiebThirring.TFFunctional.NearMinimizers

/-! # Exact-mass finite cube competitors for the TF energy

This is the step-density approximation input used by the semiclassical upper bound: every TF competitor
can be replaced, with arbitrary positive energy error, by a literal finite
regular cube mesh of the same mass. Joint density convergence controls the full
functional, including the Coulomb singularities.
-/

public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LiebThirring.TFFunctional

/-- The exact all-density step-density approximation packing input of `TFUpper.FullPotential`. -/
theorem exists_same_mass_cubeDensity_energy_approximation {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hmass : tfMass ρ = (ν : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (B : ℕ) (g : TFUpper.CubeMesh B) (σ : TFDensity),
      g.represents σ ∧ tfMass σ = (ν : ℝ) ∧
        tfFunctional a z R σ ≤ tfFunctional a z R ρ + δ := by
  obtain ⟨B, g, σ, hrep, hm, hp, h1⟩ :=
    exists_same_mass_cubeDensity_sequence ρ ν hν hmass
  have hF := tendsto_tfFunctional a z R σ ρ hp h1
  obtain ⟨j, hj⟩ := (hF.eventually
    (gt_mem_nhds (lt_add_of_pos_right (tfFunctional a z R ρ) hδ))).exists
  exact ⟨B j, g j, σ j, hrep j, hm j, hj.le⟩

end LiebThirring.TFFunctional

end
