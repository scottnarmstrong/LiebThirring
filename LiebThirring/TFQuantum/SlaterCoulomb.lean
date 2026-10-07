/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterMarginals
public import LiebThirring.Defs.Coulomb
public import LiebThirring.Defs.Density
public import LiebThirring.ThomasFermi.NuclearPotential
public import LiebThirring.Defs.KineticEnergy
import LiebThirring.Electrostatics.Gaussian
import LiebThirring.Variational.FormFinite

/-! # Direct and exchange Coulomb integrals of occupied orbitals

These integrals retain the conventional factor one half. Positivity and the
exchange bound follow from the actual projector kernel, without a finiteness
assumption. Their identification with the determinant's repulsion expectation
requires the two-particle marginal identity.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- Direct self-energy of the orbital density, with the factor one half. -/
@[expose] noncomputable def slaterDirectCoulomb {N q : ℕ}
    (u : Fin N → State 1 q) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ p : Position × Position,
    coulombKernel p.1 p.2 *
      ENNReal.ofReal (slaterOrbitalDensity u p.1 * slaterOrbitalDensity u p.2)

/-- Coulomb integral of the direct-minus-exchange kernel. -/
@[expose] noncomputable def slaterPairCoulomb {N q : ℕ}
    (u : Fin N → State 1 q) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * ∫⁻ p : Position × Position,
    coulombKernel p.1 p.2 * ENNReal.ofReal
      (slaterOrbitalDensity u p.1 * slaterOrbitalDensity u p.2 -
        slaterExchangeDensity u p.1 p.2)

theorem slaterPairCoulomb_le_direct {N q : ℕ} (u : Fin N → State 1 q) :
    slaterPairCoulomb u ≤ slaterDirectCoulomb u := by
  unfold slaterPairCoulomb slaterDirectCoulomb
  apply mul_le_mul_right
  apply lintegral_mono
  intro p
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
    (sub_le_self _ (slaterExchangeDensity_nonneg u p.1 p.2))) _

/-- The actual attraction expectation of every state is its density test. -/
theorem attraction_expectation_eq_density {N q M : ℕ} (ψ : State N q)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Position, (∑ k : Fin M, (z k : ℝ≥0∞) * coulombKernel x (R k)) *
        density ψ x := by
  let w : Position → ℝ≥0∞ := fun x => ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel x (R k)
  have hw : Measurable w := Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_coulombKernel.of_uncurry_right)
  rw [density_testing N q ψ w hw]
  change (∫⁻ X : Configuration N,
    (∑ i : Fin N, w (particlePosition X i)) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) = _
  simp only [Finset.sum_mul]
  exact lintegral_finsetSum Finset.univ fun i _ =>
    ((hw.comp (measurable_particlePosition i)).mul (measurable_state_norm_sq ψ))

/-- The extended nuclear potential agrees with the literal real potential a.e. -/
theorem nuclearPotential_ennreal_toReal {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ∀ᵐ x : Position, (∑ k : Fin M, (z k : ℝ≥0∞) * coulombKernel x (R k)).toReal =
      tfNuclearPotential z R x := by
  filter_upwards [eventually_countable_forall.mpr
    (fun k : Fin M => volume.ae_ne (R k))] with x hx
  have hfin (k : Fin M) : (z k : ℝ≥0∞) * coulombKernel x (R k) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (norm_sub_pos_iff.mpr (hx k)))))
  rw [ENNReal.toReal_sum (fun k _ => hfin k)]
  simp only [tfNuclearPotential, ENNReal.toReal_mul, ENNReal.coe_toReal,
    coulombKernel, ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _), div_eq_mul_inv]

/-- Every finite-kinetic state's real attraction is the ordinary density integral. -/
theorem attraction_expectation_toReal_eq_density {N q M : ℕ} (ψ : State N q)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal =
      ∫ x : Position, tfNuclearPotential z R x * (density ψ x).toReal := by
  let w : Position → ℝ≥0∞ := fun x => ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel x (R k)
  have hw : Measurable w := Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_coulombKernel.of_uncurry_right)
  have hf : (∫⁻ x : Position, w x * density ψ x) < ⊤ := by
    rw [← attraction_expectation_eq_density ψ z R]
    exact lintegral_attraction_lt_top z R ψ hT
  rw [attraction_expectation_eq_density ψ z R]
  refine (integral_toReal (hw.mul (measurable_density ψ)).aemeasurable
    (ae_lt_top (hw.mul (measurable_density ψ)) hf.ne)).symm.trans ?_
  apply integral_congr_ae
  filter_upwards [nuclearPotential_ennreal_toReal z R] with x hx
  change (w x * density ψ x).toReal = _
  rw [ENNReal.toReal_mul, hx]

end LiebThirring
end
