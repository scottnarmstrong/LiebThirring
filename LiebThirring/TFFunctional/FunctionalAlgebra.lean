/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Operations
public import LiebThirring.TFFunctional.DomainFinite
public import LiebThirring.TFFunctional.CoulombAlgebra
import all LiebThirring.Electrostatics.Basic

/-! # Finite Coulomb and attraction algebra on the full TF carrier

The real direct energy is expanded only after all extended positive terms
have been proved finite. Proof: the TF finiteness estimates–mass completion.
-/

public section

open MeasureTheory Finset
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem tfNuclearPotential_nonneg {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Position) : 0 ≤ tfNuclearPotential z R x := by
  unfold tfNuclearPotential
  exact sum_nonneg fun k _ => div_nonneg (z k).property (norm_nonneg _)

theorem integral_tfNuclearPotential_mul_nonneg {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ : TFDensity) :
    0 ≤ ∫ x, tfNuclearPotential z R x * ρ.val x := by
  apply integral_nonneg_of_ae
  filter_upwards [ρ.property.1] with x hx
  exact mul_nonneg (tfNuclearPotential_nonneg z R x) hx

theorem integral_tfNuclearPotential_mul_add {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ σ : TFDensity) :
    (∫ x, tfNuclearPotential z R x * (tfDensityAdd ρ σ).val x) =
      (∫ x, tfNuclearPotential z R x * ρ.val x) +
        ∫ x, tfNuclearPotential z R x * σ.val x := by
  have heq : (fun x => tfNuclearPotential z R x * (tfDensityAdd ρ σ).val x) =ᵐ[volume]
      fun x => tfNuclearPotential z R x * (ρ.val x + σ.val x) := by
    filter_upwards [tfDensityAdd_coeFn ρ σ] with x hx
    rw [hx]
  rw [integral_congr_ae heq]
  simp_rw [mul_add]
  exact integral_add (integrable_tfNuclearPotential_mul z R ρ)
    (integrable_tfNuclearPotential_mul z R σ)

theorem tfCoulombEnergy_symm (ρ σ : TFDensity) :
    tfCoulombEnergy ρ σ = tfCoulombEnergy σ ρ := by
  unfold tfCoulombEnergy
  rw [coulombEnergy_symm]

/-- Uniform potential bounds control both the mixed and self interaction. -/
theorem tfCoulombEnergy_le_of_potential_le (ρ σ : TFDensity) (η : ℝ)
    (hη : 0 ≤ η)
    (hpotential : ∀ x, coulombPotential (tfDensityMeasure σ) x ≤ ENNReal.ofReal η) :
    tfCoulombEnergy ρ σ ≤ η * tfMass ρ / 2 := by
  have he : coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) ≤
      ENNReal.ofReal (η * tfMass ρ) := by
    rw [coulombEnergy_eq_lintegral]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal η ∂tfDensityMeasure ρ :=
        lintegral_mono hpotential
      _ = ENNReal.ofReal (η * tfMass ρ) := by
        rw [lintegral_const, tfDensityMeasure_univ, ENNReal.ofReal_mul hη]
  unfold tfCoulombEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  have ht := (ENNReal.toReal_le_toReal (coulombEnergy_tfDensity_lt_top ρ σ).ne
    ENNReal.ofReal_ne_top).mpr he
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hη (tfMass_nonneg ρ))] using ht

theorem tfCoulombEnergy_add_self (ρ σ : TFDensity) :
    tfCoulombEnergy (tfDensityAdd ρ σ) (tfDensityAdd ρ σ) =
      tfCoulombEnergy ρ ρ + 2 * tfCoulombEnergy ρ σ + tfCoulombEnergy σ σ := by
  have haa := (coulombEnergy_tfDensity_lt_top ρ ρ).ne
  have hab := (coulombEnergy_tfDensity_lt_top ρ σ).ne
  have hba := (coulombEnergy_tfDensity_lt_top σ ρ).ne
  have hbb := (coulombEnergy_tfDensity_lt_top σ σ).ne
  unfold tfCoulombEnergy
  rw [tfDensityMeasure_tfDensityAdd]
  simp_rw [coulombEnergy_add_left, coulombEnergy_add_right]
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨haa, hab⟩)
    (ENNReal.add_ne_top.mpr ⟨hba, hbb⟩), ENNReal.toReal_add haa hab,
    ENNReal.toReal_add hba hbb, coulombEnergy_symm (tfDensityMeasure σ) (tfDensityMeasure ρ)]
  ring

end LiebThirring.TFFunctional

end
