/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.Variational
public import LiebThirring.TFUpper.Correction
import LiebThirring.TFFunctional.CubeEnergyApproximation

/-! # The full-potential upper bound with exact particle number

The conditional full-potential upper bound assembly uses only explicit external cube spectral theory/sharp eigenvalue sums/filled-density convergence
inputs. The proved TF finiteness estimates/step-density approximation/Slater construction APIs supply interaction continuity, exact-mass
cube approximation, and the determinant. The exact-number correction is proved
in `Correction` and is called here. The trial and TF energies are variational infima; the nuclear
potential is uncut. There is no neutrality or minimizer assumption.

Source: Lieb–Simon (1977) III.5 (74)--(78), pp. 72--73.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LiebThirring.TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- Conditional full-potential upper bound in the integer-particle scaling
`α_j = N_j / ν`, for every positive `ν`, including above neutrality. -/
theorem eventually_full_potential_upper_of_external_inputs
    (q : {q : ℕ // 1 ≤ q}) (ν : ℝ≥0) (hν : 0 < ν) {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hN14_N20 : ∀ (B : ℕ) (g : CubeMesh B) (σ : TFDensity), g.represents σ →
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
          S < ‖x‖ → orbitalValue (u j i) x = 0))
    (hN15 : ∀ (B : ℕ) (g : CubeMesh B),
      Tendsto (fun j => (((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(5 : ℝ) / 3) *
        occupiedCubeKinetic q.val (show 0 < q.val from q.property) g.side
          ((N j : ℝ≥0) / ν) g.mass) atTop
        (𝓝 ((tfKineticConstant q).val *
          (g.side.val⁻¹ ^ 2 * ∑ b, (g.mass b : ℝ) ^ ((5 : ℝ) / 3)))))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
        electronicGroundStateEnergy (N j) q.val M
          (fun k => ((N j : ℝ≥0) / ν) * z k)
          (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k) ≤
        (((tfEnergy (tfKineticConstant q) ν z R).toReal + ε : ℝ) : EReal) := by
  let α : ℕ → ℝ≥0 := fun j => (N j : ℝ≥0) / ν
  have hα := eventually_chargeScale_pos ν hν N hN
  have hδ : 0 < ε / 4 := by linarith only [hε]
  obtain ⟨ρ, hρmass, hρenergy⟩ :=
    exists_exact_mass_tfFunctional_lt (tfKineticConstant q) ν z R (ε / 4) hδ
  obtain ⟨B, g, σ, hstep, hσmass, hσenergy⟩ :=
    TFFunctional.exists_same_mass_cubeDensity_energy_approximation
      (tfKineticConstant q) ν hν z R ρ hρmass (ε / 4) hδ
  obtain ⟨u, d, hu, hf, hK, hd, hLp, hL1, hsupp⟩ := hN14_N20 B g σ hstep
  obtain ⟨ψ, _, hupper⟩ := exists_approximate_slater_trials_of_external_inputs
    q g σ hstep z R α hα u d hu hf hK hd hLp hL1 (hN15 B g)
  have hmass : ∑ b, (g.mass b : ℝ) = (ν : ℝ) :=
    (g.mass_eq σ hstep).symm.trans hσmass
  filter_upwards [hα, hupper (ε / 4) hδ] with j hj hjupper
  have hcount := occupationCount_le_particleNumber (α j) ν g.mass hmass (N j)
    (particleNumber_eq_scale_mul_mass ν hν (N j))
  obtain ⟨S, hS, hs⟩ := hsupp j
  obtain ⟨χ, hχ⟩ := exists_exact_particle_trial q (α j) z R
    (u j) (hu j) (hf j) S hS hs (TFFunctional.tfDensitySMul (α j) (d j))
      (hd j) (N j) hcount (ε / 4) hδ
  have htrial := scaled_electronicGroundStateEnergy_le_trial (α j) hj z R χ
  apply htrial.trans
  apply EReal.coe_le_coe_iff.mpr
  linarith only [hχ, hjupper.1, hσenergy, hρenergy]

end LiebThirring.TFUpper
end
