/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.NearEstimate
import LiebThirring.TFFunctional.DensityBasic
import LiebThirring.Electrostatics.CoulombPositivity

/-! # Finiteness of Coulomb energy on the Thomas–Fermi carrier

The near integral at radius one is bounded by Hölder. The complementary
kernel is at most one. These estimates prove finiteness without adding a
Coulomb-finiteness premise to the density carrier (the TF finiteness estimates).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring.TFCoulomb

/-- A TF density gives a finite measure, from its literal mass. -/
theorem isFiniteMeasure_tfDensityMeasure (ρ : TFDensity) :
    IsFiniteMeasure (tfDensityMeasure ρ) := by
  constructor
  rw [TFFunctional.tfDensityMeasure_univ]
  exact ENNReal.ofReal_lt_top

/-- The unit-radius near kernel plus one bounds the full Coulomb kernel. -/
theorem coulombKernel_le_near_add_one (x y : Position) :
    coulombKernel x y ≤ nearCoulombKernel 1 x y + 1 := by
  by_cases h : ‖x - y‖ < 1
  · rw [nearCoulombKernel, ite_eq_left h]
    exact le_add_right le_rfl
  · rw [nearCoulombKernel, ite_eq_right h, zero_add]
    unfold coulombKernel
    calc
      (ENNReal.ofReal ‖x - y‖)⁻¹ ≤ (1 : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt h))
      _ = 1 := inv_one

/-- A uniform one-center bound on the full TF Coulomb potential. -/
theorem lintegral_coulombKernel_tfDensity_le (ρ : TFDensity) (x : Position) :
    (∫⁻ y, coulombKernel x y ∂tfDensityMeasure ρ) ≤
      ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5)) *
        eLpNorm (fun y : Position => ρ.val y) ((5 : ℝ≥0∞) / 3) volume +
          ENNReal.ofReal (tfMass ρ) := by
  calc
    _ ≤ ∫⁻ y, nearCoulombKernel 1 x y + 1 ∂tfDensityMeasure ρ :=
      lintegral_mono (coulombKernel_le_near_add_one x)
    _ = (∫⁻ y, nearCoulombKernel 1 x y ∂tfDensityMeasure ρ) +
        ENNReal.ofReal (tfMass ρ) := by
      rw [lintegral_add_left (measurable_nearCoulombKernel_right 1 x),
        lintegral_const, one_mul, TFFunctional.tfDensityMeasure_univ]
    _ ≤ _ := by
      have h := lintegral_near_coulombKernel_tfDensity_le ρ 1 zero_lt_one x
      simp only [Real.one_rpow, mul_one] at h
      exact add_le_add h le_rfl

/-- A finite explicit upper bound for the mutual Coulomb energy of TF densities. -/
theorem tf_mutual_coulombEnergy_le (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) ≤
      (ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5)) *
        eLpNorm (fun y : Position => σ.val y) ((5 : ℝ≥0∞) / 3) volume +
          ENNReal.ofReal (tfMass σ)) * ENNReal.ofReal (tfMass ρ) := by
  rw [coulombEnergy_eq_lintegral]
  calc
    _ ≤ ∫⁻ _x : Position,
        ENNReal.ofReal ((8 * Real.pi) ^ ((2 : ℝ) / 5)) *
          eLpNorm (fun y : Position => σ.val y) ((5 : ℝ≥0∞) / 3) volume +
            ENNReal.ofReal (tfMass σ) ∂tfDensityMeasure ρ :=
      lintegral_mono (lintegral_coulombKernel_tfDensity_le σ)
    _ = _ := by rw [lintegral_const, TFFunctional.tfDensityMeasure_univ]

/-- Mutual Coulomb energy is finite for every pair of TF densities. -/
theorem tf_mutual_coulombEnergy_ne_top (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (tf_mutual_coulombEnergy_le ρ σ)
  exact (ENNReal.mul_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Lp.memLp σ.val).eLpNorm_lt_top, ENNReal.ofReal_lt_top⟩)
    ENNReal.ofReal_lt_top).ne

/-- Diagonal Coulomb energy is finite on the literal TF carrier. -/
theorem tf_coulombEnergy_ne_top (ρ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure ρ) ≠ ⊤ :=
  tf_mutual_coulombEnergy_ne_top ρ ρ

end LiebThirring.TFCoulomb

end
