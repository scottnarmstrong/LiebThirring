/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.Occupation
public import LiebThirring.TFUpper.CubeStep
public import LiebThirring.TFUpper.SlaterBound
import LiebThirring.TFFunctional.Continuity

/-! # Approximate-number Slater trials from filled cubes

This is the Slater upper bound assembly conditional on the external cube spectral theory/sharp eigenvalue sums/filled-density convergence
construction and identities. The proved TF finiteness estimates continuity and Slater construction Slater APIs
supply the interaction limits and normalized determinant. Every external input is
written as an explicit theorem-type argument; none assumes a many-body
energy bound. The cube mass and kinetic-moment identities, removal of
exchange, and passage to an eventual upper bound are proved here.

Source: Lieb–Simon (1977) III.11, III.13–III.14 and III.5 (74)–(78), pp. 66–73.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LiebThirring.TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- Conditional Slater upper bound for a fixed literal cube density. The selected orbitals
occupy exactly the floored particle count; Slater construction supplies the actual determinant. -/
theorem exists_approximate_slater_trials_of_external_inputs
    (q : {q : ℕ // 1 ≤ q}) {B M : ℕ} (g : CubeMesh B)
    (ρ : TFDensity) (hstep : g.represents ρ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (α : ℕ → ℝ≥0) (hα : ∀ᶠ j in atTop, 0 < α j)
    (u : (j : ℕ) → Fin (occupationCount (α j) g.mass) → State 1 q.val)
    (d : ℕ → TFDensity)
    (hN14_orthonormal : ∀ j, Orthonormal ℂ (u j))
    (hN14_finite : ∀ j i, kineticEnergy (u j i) < ⊤)
    (hN14_kinetic : ∀ j, (∑ i, (kineticEnergy (u j i)).toReal) =
      occupiedCubeKinetic q.val (show 0 < q.val from q.property) g.side (α j) g.mass)
    (hN20_density : ∀ j, ∀ᵐ x : Position,
      (TFFunctional.tfDensitySMul (α j) (d j)).val x = slaterOrbitalDensity (u j) x)
    (hN20_Lp : Tendsto (fun j => (d j).val) atTop (𝓝 ρ.val))
    (hN20_L1 : Tendsto (fun j => ∫ x : Position, |(d j).val x - ρ.val x|)
      atTop (𝓝 (0 : ℝ)))
    (hN15_lattice : Tendsto (fun j => (α j : ℝ) ^ (-(5 : ℝ) / 3) *
      occupiedCubeKinetic q.val (show 0 < q.val from q.property) g.side (α j) g.mass)
      atTop (𝓝 ((tfKineticConstant q).val *
        (g.side.val⁻¹ ^ 2 * ∑ b, (g.mass b : ℝ) ^ ((5 : ℝ) / 3))))) :
    ∃ ψ : (j : ℕ) → ElectronicTrial (occupationCount (α j) g.mass) q.val,
      (∀ j, ∀ᵐ X : Configuration (occupationCount (α j) g.mass),
        (ψ j).val.val X = slaterAmplitude (u j) X) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        orbitalUpperEnergy (α j) z R (u j) ≤ tfFunctional (tfKineticConstant q) z R ρ + ε ∧
        dilatedElectronicEnergy (α j) z R (ψ j).val ≤
          tfFunctional (tfKineticConstant q) z R ρ + ε := by
  classical
  have hex (j : ℕ) := exists_slater_trial_of_orthonormal (u j) (hN14_orthonormal j) (hN14_finite j)
  choose ψ hψamp hψT hψρ hψB using hex
  refine ⟨ψ, hψamp, ?_⟩
  have hK : Tendsto (fun j => (α j : ℝ) ^ (-(5 : ℝ) / 3) *
      ∑ i, (kineticEnergy (u j i)).toReal) atTop
      (𝓝 ((tfKineticConstant q).val * ∫ x : Position, ρ.val x ^ ((5 : ℝ) / 3))) := by
    simp_rw [hN14_kinetic]
    rw [g.kinetic_moment_eq ρ hstep]
    exact hN15_lattice
  have hE : Tendsto (fun j => orbitalUpperEnergy (α j) z R (u j)) atTop
      (𝓝 (tfFunctional (tfKineticConstant q) z R ρ)) := by
    have h := (hK.sub (TFFunctional.tendsto_integral_tfNuclearPotential_mul
      z R d ρ hN20_Lp hN20_L1)).add
      (TFFunctional.tendsto_tfCoulombEnergy_self d ρ hN20_Lp hN20_L1)
    apply h.congr'
    filter_upwards [hα] with j hj
    exact (orbitalUpperEnergy_eq_divided_density (α j) hj z R (u j) (d j)
      (hN20_density j)).symm
  intro ε hε
  filter_upwards [hE.eventually_lt_const (lt_add_of_pos_right _ hε)] with j hj
  refine ⟨hj.le, ?_⟩
  exact (dilatedElectronicEnergy_le_orbitalUpperEnergy_of_slater_identities
    (α j) z R (u j) (TFFunctional.tfDensitySMul (α j) (d j)) (hN20_density j)
    (ψ j) (hψT j) (hψρ j) (hψB j)).trans hj.le

end LiebThirring.TFUpper
end
