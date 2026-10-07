/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DiffuseKinetic
public import LiebThirring.TFFunctional.UniformDiffuse
public import LiebThirring.TFFunctional.FunctionalAlgebra
public import LiebThirring.TFFunctional.Variational

/-! # Completion of relaxed TF trials to the exact mass

A diffuse nonnegative cloud supplies the missing mass. Its kinetic increment,
mixed Coulomb term, and self interaction tend to zero; its nuclear attraction
can only improve the upper bound. This proves mass completion on the full carrier.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem exists_tfDensity_mass_completion {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : TFDensity, tfMass σ = (ν : ℝ) ∧
      tfFunctional a z R σ ≤ tfFunctional a z R ρ + ε := by
  let t : ℝ≥0 := ⟨(ν : ℝ) - tfMass ρ, sub_nonneg.mpr hmass⟩
  have ht : (t : ℝ) ≤ (ν : ℝ) := by
    change (ν : ℝ) - tfMass ρ ≤ (ν : ℝ)
    linarith only [tfMass_nonneg ρ]
  let η : ℝ := ε / (2 * (tfMass ρ + (ν : ℝ) + 1))
  have hden : 0 < tfMass ρ + (ν : ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (tfMass_nonneg ρ) ν.property) zero_lt_one
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hden)
  have hcancel : η * (tfMass ρ + (ν : ℝ) + 1) = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt hden]
  have hk : Tendsto (fun j => a.val *
      ((∫ x : Position, ((tfDensityAdd ρ (tfDiffuseDensity t j)).val x) ^ ((5 : ℝ) / 3)) -
        ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3))) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_kinetic_add_tfDiffuseDensity ρ t).sub
        (tendsto_const_nhds (x := ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)))).const_mul a.val
  obtain ⟨j, hjk, hjp⟩ := ((hk.eventually_lt_const (half_pos hε)).and
    (eventually_coulombPotential_tfDiffuseDensity_le t η hη)).exists
  refine ⟨tfDensityAdd ρ (tfDiffuseDensity t j), ?_, ?_⟩
  · rw [tfMass_tfDensityAdd, tfMass_tfDiffuseDensity]
    change tfMass ρ + ((ν : ℝ) - tfMass ρ) = (ν : ℝ)
    ring
  · have hcross := tfCoulombEnergy_le_of_potential_le ρ (tfDiffuseDensity t j) η hη.le hjp
    have hself := tfCoulombEnergy_le_of_potential_le
      (tfDiffuseDensity t j) (tfDiffuseDensity t j) η hη.le hjp
    rw [tfMass_tfDiffuseDensity] at hself
    have hself' : tfCoulombEnergy (tfDiffuseDensity t j) (tfDiffuseDensity t j) ≤
        η * (ν : ℝ) / 2 := hself.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hη.le) (by norm_num))
    have hn := integral_tfNuclearPotential_mul_nonneg z R (tfDiffuseDensity t j)
    have hην : 0 ≤ η * (ν : ℝ) := mul_nonneg hη.le ν.property
    have hrest : 2 * tfCoulombEnergy ρ (tfDiffuseDensity t j) +
        tfCoulombEnergy (tfDiffuseDensity t j) (tfDiffuseDensity t j) ≤ ε / 2 := by
      nlinarith only [hcross, hself', hcancel, hη, hην]
    have hkin : a.val * (∫ x : Position,
        ((tfDensityAdd ρ (tfDiffuseDensity t j)).val x) ^ ((5 : ℝ) / 3)) ≤
        a.val * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) + ε / 2 := by
      nlinarith only [hjk]
    unfold tfFunctional
    rw [integral_tfNuclearPotential_mul_add, tfCoulombEnergy_add_self]
    linarith only [hkin, hn, hrest]

theorem tfEnergy_eq_tfRelaxedEnergy_library {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    tfEnergy a ν z R = tfRelaxedEnergy a ν z R :=
  tfEnergy_eq_tfRelaxedEnergy_of_mass_completion a ν z R
    (exists_tfDensity_mass_completion a ν z R)

/-- Enlarging the exact mass cannot increase the TF infimum. -/
theorem tfEnergy_antitone {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Antitone (fun ν : ℝ≥0 => tfEnergy a ν z R) := by
  intro ν₁ ν₂ hν
  change tfEnergy a ν₂ z R ≤ tfEnergy a ν₁ z R
  rw [tfEnergy_eq_tfRelaxedEnergy_library, tfEnergy_eq_tfRelaxedEnergy_library]
  exact tfRelaxedEnergy_antitone a hν z R

end LiebThirring.TFFunctional

end
