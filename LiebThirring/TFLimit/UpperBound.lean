/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLimit.UpperKinetic
public import LiebThirring.TFUpper.FullPotential

/-! # The full-potential upper bound upper input for the Thomas–Fermi limit assembly

The proved conditional full-potential upper bound theorem supplies the exact `hupper` predicate of
`ElectronicLimit` and `TotalEnergy`. Its external cube spectral theory/filled-density convergence hypothesis is retained verbatim. The proved sharp eigenvalue sums lattice
limit supplies the kinetic hypothesis internally.

Source: Lieb–Simon (1977) III.5 (74)--(78), pp. 72--73.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LiebThirring.TFLimit
open TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- The exact upper-bound input of both conditional limit consumers, supplied
by full-potential upper bound with its remaining external cube spectral theory/filled-density convergence input and the proved sharp eigenvalue sums limit. -/
theorem scaledElectronicEnergy_eventually_le_of_external_inputs
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
    : ∀ (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
      scaledElectronicEnergy (N j) q.val M ((N j : ℝ≥0) / ν) z R ≤
        (((tfEnergy (tfKineticConstant q) ν z R).toReal + ε : ℝ) : EReal) := by
  intro ε hε
  exact eventually_full_potential_upper_of_external_inputs
    q ν hν z R N hN hN14_N20
    (fun _ g => tendsto_scaled_occupiedCubeKinetic q ν hν N hN g) ε hε

end LiebThirring.TFLimit
end
