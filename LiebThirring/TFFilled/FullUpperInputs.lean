/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.FilledInputs
public import LiebThirring.TFFilled.MeshLatticeConvergence
public import LiebThirring.TFUpper.FilledKinetic
public import LiebThirring.TFLimit.UpperBound

/-! # The complete cube-orbital input for the Thomas–Fermi upper bound

The Dirichlet orbital estimates supply the explicit orbital orthonormality, finite/exact kinetic energy
and support. The lattice density estimates supply the proved scalar density limits, and TFFilled supplies
the literal orbital-density identification on the carrier. Together they
prove exactly the remaining cube spectral theory/filled-density convergence predicate of TFLimit.UpperBound.
Source: Lieb–Simon (1977) III.14 (68)–(71), pp.69–71; III.5 (74)–(78), pp.72–73;

-/

public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace LiebThirring.TFFilled
open TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨one_le_five_thirds⟩

/-- The two orbital definitions denote the same enumerated family. -/
theorem cubeTrialOrbitals_eq_filledCubeOrbitals
    {B : ℕ} (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (a : ℝ≥0) :
    cubeTrialOrbitals q g a = filledCubeOrbitals q g a := rfl

/-- The exact remaining `hN14_N20` input of the molecular upper bound.
All orbital, kinetic, density, convergence and support assertions are proved. -/
theorem exists_scaled_cube_orbital_density_inputs
    (q : {q : ℕ // 1 ≤ q}) (ν : ℝ≥0) (hν : 0 < ν)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∀ (B : ℕ) (g : CubeMesh B) (σ : TFDensity), g.represents σ →
      ∃ (u : (j : ℕ) → Fin (occupationCount ((N j : ℝ≥0) / ν) g.mass) → State 1 q.val)
        (d : ℕ → TFDensity),
        (∀ j, Orthonormal ℂ (u j)) ∧
        (∀ j i, kineticEnergy (u j i) < ⊤) ∧
        (∀ j, (∑ i, (kineticEnergy (u j i)).toReal) =
          occupiedCubeKinetic q.val (show 0 < q.val from q.property) g.side
            ((N j : ℝ≥0) / ν) g.mass) ∧
        (∀ j, ∀ᵐ x : Position,
          (TFFunctional.tfDensitySMul ((N j : ℝ≥0) / ν) (d j)).val x =
            slaterOrbitalDensity (u j) x) ∧
        Tendsto (fun j => (d j).val) atTop (𝓝 σ.val) ∧
        Tendsto (fun j => ∫ x : Position, |(d j).val x - σ.val x|) atTop (𝓝 (0 : ℝ)) ∧
        (∀ j, ∃ S : ℝ, 0 ≤ S ∧ ∀ i, ∀ᵐ x : Position,
          S < ‖x‖ → orbitalValue (u j i) x = 0) := by
  intro B g σ hstep
  let a : ℕ → ℝ≥0 := fun j => (N j : ℝ≥0) / ν
  have ha : Tendsto (fun j => (a j : ℝ)) atTop atTop :=
    TFLimit.tendsto_largeCharge_parameter ν hν N hN
  refine ⟨fun j => cubeTrialOrbitals q g (a j),
    fun j => normalizedMeshDensity q.val q.property g (a j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => orthonormal_cubeTrialOrbitals q g (a j)
  · exact fun j i => kineticEnergy_cubeTrialOrbitals_lt_top q g (a j) i
  · exact fun j => sum_kineticEnergy_cubeTrialOrbitals q g (a j)
  · intro j
    change (TFFunctional.tfDensitySMul (a j)
      (normalizedMeshDensity q.val q.property g (a j))).val =ᵐ[volume]
        slaterOrbitalDensity (cubeTrialOrbitals q g (a j))
    rw [cubeTrialOrbitals_eq_filledCubeOrbitals]
    exact tfDensitySMul_normalizedMeshDensity_filledCubeOrbitals_ae q g (a j)
  · exact tendsto_normalizedMeshDensity_of_lattice q.val q.property g σ hstep ha
  · exact tendsto_integral_abs_normalizedMeshDensity_sub_of_lattice
      q.val q.property g σ hstep ha
  · exact fun j => cubeTrialOrbitals_compact_support q g (a j)

/-- The full Thomas–Fermi electronic upper estimate, with no external
cube-orbital, density-convergence or kinetic-asymptotic premise. -/
theorem scaledElectronicEnergy_eventually_le
    (q : {q : ℕ // 1 ≤ q}) (ν : ℝ≥0) (hν : 0 < ν) {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∀ (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
      TFLimit.scaledElectronicEnergy (N j) q.val M ((N j : ℝ≥0) / ν) z R ≤
        (((tfEnergy (tfKineticConstant q) ν z R).toReal + ε : ℝ) : EReal) :=
  TFLimit.scaledElectronicEnergy_eventually_le_of_external_inputs q ν hν z R N hN
    (exists_scaled_cube_orbital_density_inputs q ν hν N hN)

end LiebThirring.TFFilled
end
