/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DensityBridge
public import LiebThirring.TFQuantum.DilationLargeCharge
public import LiebThirring.TFQuantum.SlaterTrial
public import LiebThirring.ThomasFermi.KineticConstant

/-! # Slater upper bounds in the exact large-charge normalization

These helpers consume the proved Slater construction determinant identities. They use
states and the uncut nuclear potential.
Exchange is dropped by a proved positive extended-integral inequality,
after finiteness of the direct term has been established. No estimate of
the size of exchange is needed. Source: Lieb–Simon (1977) III.11, p. 66.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace LiebThirring.TFUpper

/-- The proved Slater construction API produces a normalized trial with raw extended identities. -/
theorem exists_slater_trial_of_orthonormal {n q : ℕ} (u : Fin n → State 1 q)
    (hu : Orthonormal ℂ u) (hf : ∀ i, kineticEnergy (u i) < ⊤) :
    ∃ ψ : ElectronicTrial n q,
      (∀ᵐ X : Configuration n, ψ.val.val X = slaterAmplitude u X) ∧
      kineticEnergy ψ.val.val = ∑ i, kineticEnergy (u i) ∧
      (∀ᵐ x : Position, density ψ.val.val x = ENNReal.ofReal (slaterOrbitalDensity u x)) ∧
      (∫⁻ X : Configuration n, electronRepulsion X * (‖ψ.val.val X‖₊ : ℝ≥0∞) ^ 2) =
        slaterPairCoulomb u := by
  refine ⟨slaterElectronicTrial u hu hf, ?_⟩
  change (∀ᵐ X : Configuration n, slaterState u X = slaterAmplitude u X) ∧
    kineticEnergy (slaterState u) = ∑ i, kineticEnergy (u i) ∧
    (∀ᵐ x : Position, density (slaterState u) x = ENNReal.ofReal (slaterOrbitalDensity u x)) ∧
    (∫⁻ X : Configuration n, electronRepulsion X * (‖slaterState u X‖₊ : ℝ≥0∞) ^ 2) =
      slaterPairCoulomb u
  exact ⟨coeFn_slaterState u, kineticEnergy_slaterState u hu,
    density_slaterState u hu, electronRepulsion_slaterState u hu⟩

/-- The direct upper energy of occupied orbitals in scaled coordinates. -/
@[expose] noncomputable def orbitalUpperEnergy {n q M : ℕ} (α : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (u : Fin n → State 1 q) : ℝ :=
  (α : ℝ) ^ (-(5 : ℝ) / 3) * ∑ i, (kineticEnergy (u i)).toReal +
    (α : ℝ) ^ (-(2 : ℝ)) * (slaterDirectCoulomb u).toReal -
    (α : ℝ) ^ (-(1 : ℝ)) *
      ∫ x : Position, tfNuclearPotential z R x * slaterOrbitalDensity u x

/-- Conditional only on the literal kinetic and marginal identities of Slater construction. -/
theorem dilatedElectronicEnergy_le_orbitalUpperEnergy_of_slater_identities
    {n q M : ℕ} (α : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : Fin n → State 1 q) (d : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x)
    (ψ : ElectronicTrial n q)
    (hT : kineticEnergy ψ.val.val = ∑ i, kineticEnergy (u i))
    (hρ : ∀ᵐ x : Position, density ψ.val.val x = ENNReal.ofReal (slaterOrbitalDensity u x))
    (hB : (∫⁻ X : Configuration n,
      electronRepulsion X * (‖ψ.val.val X‖₊ : ℝ≥0∞) ^ 2) = slaterPairCoulomb u) :
    dilatedElectronicEnergy α z R ψ.val ≤ orbitalUpperEnergy α z R u := by
  have hDf := slaterDirectCoulomb_lt_top_of_tfDensity u d hd
  have hTf : ∀ i, kineticEnergy (u i) ≠ ⊤ := by
    intro i
    apply ne_top_of_le_ne_top ψ.val.property.2.ne
    rw [hT]
    exact Finset.single_le_sum (f := fun i => kineticEnergy (u i))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  have hTr : (kineticEnergy ψ.val.val).toReal = ∑ i, (kineticEnergy (u i)).toReal := by
    rw [hT, ENNReal.toReal_sum (fun i _ => hTf i)]
  have hBreal : (slaterPairCoulomb u).toReal ≤ (slaterDirectCoulomb u).toReal :=
    ENNReal.toReal_mono hDf.ne (slaterPairCoulomb_le_direct u)
  have hA : (∫⁻ X : Configuration n,
      attraction z R X * (‖ψ.val.val X‖₊ : ℝ≥0∞) ^ 2).toReal =
      ∫ x : Position, tfNuclearPotential z R x * slaterOrbitalDensity u x := by
    rw [attraction_expectation_toReal_eq_density ψ.val.val z R ψ.val.property.2]
    apply integral_congr_ae
    filter_upwards [hρ] with x hx
    rw [hx, ENNReal.toReal_ofReal (slaterOrbitalDensity_nonneg u x)]
  unfold dilatedElectronicEnergy orbitalUpperEnergy
  rw [hTr, hB, hA]
  exact sub_le_sub_right (add_le_add_right
    (mul_le_mul_of_nonneg_left hBreal (Real.rpow_nonneg α.property _)) _) _

/-- A genuine Slater trial obeys the direct upper bound in scaled coordinates. -/
theorem exists_dilated_slater_trial_le {n q M : ℕ}
    (α : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : Fin n → State 1 q) (d : TFDensity)
    (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x)
    (hu : Orthonormal ℂ u) (hf : ∀ i, kineticEnergy (u i) < ⊤) :
    ∃ ψ : ElectronicTrial n q,
      dilatedElectronicEnergy α z R ψ.val ≤ orbitalUpperEnergy α z R u := by
  obtain ⟨ψ, _, hT, hρ, hB⟩ := exists_slater_trial_of_orthonormal u hu hf
  exact ⟨ψ, dilatedElectronicEnergy_le_orbitalUpperEnergy_of_slater_identities
    α z R u d hd ψ hT hρ hB⟩

/-- An actual normalized trial bounds the physical scaled electronic infimum. -/
theorem scaled_electronicGroundStateEnergy_le_trial {n q M : ℕ}
    (α : ℝ≥0) (hα : 0 < α) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ψ : ElectronicTrial n q) :
    (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
      electronicGroundStateEnergy n q M (fun k => α * z k)
        (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) ≤
      (dilatedElectronicEnergy α z R ψ.val : EReal) := by
  rw [electronicGroundStateEnergy_largeCharge_dilation α hα z R]
  exact iInf_le _ ψ

/-- The direct upper energy depends on the divided density in TF coordinates. -/
theorem orbitalUpperEnergy_eq_divided_density {n q M : ℕ}
    (α : ℝ≥0) (hα : 0 < α) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : Fin n → State 1 q) (d : TFDensity)
    (hd : ∀ᵐ x : Position,
      (TFFunctional.tfDensitySMul α d).val x = slaterOrbitalDensity u x) :
    orbitalUpperEnergy α z R u =
      (α : ℝ) ^ (-(5 : ℝ) / 3) * ∑ i, (kineticEnergy (u i)).toReal -
        (∫ x : Position, tfNuclearPotential z R x * d.val x) + tfCoulombEnergy d d := by
  have hA : (∫ x : Position, tfNuclearPotential z R x * slaterOrbitalDensity u x) =
      (α : ℝ) * ∫ x : Position, tfNuclearPotential z R x * d.val x := by
    rw [← integral_nuclearPotential_smul α z R d]
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx]
  have hD := slaterDirectCoulomb_toReal_eq_tfDensity u (TFFunctional.tfDensitySMul α d) hd
  rw [tfCoulombEnergy_smul] at hD
  have hαr : (α : ℝ) ≠ 0 := (show 0 < (α : ℝ) from hα).ne'
  have hcD : (α : ℝ) ^ (-(2 : ℝ)) * (α : ℝ) ^ 2 = 1 := by
    erw [Real.rpow_neg α.property, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 hαr)]
  have hcA : (α : ℝ) ^ (-(1 : ℝ)) * (α : ℝ) = 1 := by
    erw [Real.rpow_neg α.property, Real.rpow_one, inv_mul_cancel₀ hαr]
  unfold orbitalUpperEnergy
  rw [hD, hA, ← mul_assoc, hcD, one_mul, ← mul_assoc, hcA, one_mul]
  ring

end LiebThirring.TFUpper
end
