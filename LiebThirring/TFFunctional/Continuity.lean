/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.PotentialDifference
public import LiebThirring.TFFunctional.AttractionCoercivity

/-! # Joint L1 and L5/3 continuity of Thomas--Fermi interaction terms -/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

theorem abs_integral_tfNuclearPotential_mul_sub_le {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ σ : TFDensity) :
    |(∫ x : Position, tfNuclearPotential z R x * ρ.val x) -
        ∫ x : Position, tfNuclearPotential z R x * σ.val x| ≤
      attractionKineticCoefficient z * ‖ρ.val - σ.val‖ +
        totalNuclearCharge z * ∫ x : Position, |ρ.val x - σ.val x| := by
  let δ := tfDensityAbsDiff ρ σ
  have hiρ := integrable_tfNuclearPotential_mul z R ρ
  have hiσ := integrable_tfNuclearPotential_mul z R σ
  have hdiff : (fun x : Position => |tfNuclearPotential z R x * ρ.val x -
      tfNuclearPotential z R x * σ.val x|) =ᵐ[volume]
      fun x => tfNuclearPotential z R x * δ.val x := by
    filter_upwards [tfDensityAbsDiff_apply_ae ρ σ] with x hx
    rw [hx]
    have hv := tfNuclearPotential_nonneg z R x
    rw [← mul_sub, abs_mul, abs_of_nonneg hv]
  calc
    _ = |∫ x : Position, (tfNuclearPotential z R x * ρ.val x -
        tfNuclearPotential z R x * σ.val x)| := by rw [integral_sub hiρ hiσ]
    _ ≤ ∫ x : Position, |tfNuclearPotential z R x * ρ.val x -
        tfNuclearPotential z R x * σ.val x| := abs_integral_le_integral_abs
    _ = ∫ x : Position, tfNuclearPotential z R x * δ.val x :=
      integral_congr_ae hdiff
    _ ≤ attractionKineticCoefficient z *
          (∫ x : Position, (δ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) +
        totalNuclearCharge z * tfMass δ := integral_tfNuclearPotential_mul_le z R δ
    _ = _ := by
      rw [integral_tfDensity_rpow_eq_norm, tfMass_tfDensityAbsDiff,
        norm_tfDensityAbsDiff]
      have hn : 0 ≤ ‖ρ.val - σ.val‖ := norm_nonneg _
      rw [← Real.rpow_mul hn]
      norm_num

theorem tendsto_integral_tfNuclearPotential_mul {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val))
    (hL1 : Tendsto (fun j => ∫ x : Position, |(f j).val x - σ.val x|)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => ∫ x : Position, tfNuclearPotential z R x * (f j).val x) atTop
      (𝓝 (∫ x : Position, tfNuclearPotential z R x * σ.val x)) := by
  have hn : Tendsto (fun j => ‖(f j).val - σ.val‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hLp.sub_const σ.val).norm
  have hb : Tendsto (fun j =>
      attractionKineticCoefficient z * ‖(f j).val - σ.val‖ +
        totalNuclearCharge z * ∫ x : Position, |(f j).val x - σ.val x|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hn).add (tendsto_const_nhds.mul hL1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hb
  obtain ⟨J, hJ⟩ := hb ε hε
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq]
  apply (abs_integral_tfNuclearPotential_mul_sub_le z R (f j) σ).trans_lt
  have hbound : 0 ≤ attractionKineticCoefficient z * ‖(f j).val - σ.val‖ +
      totalNuclearCharge z * ∫ x : Position, |(f j).val x - σ.val x| := by
    exact add_nonneg
      (mul_nonneg (attractionKineticCoefficient_nonneg z) (norm_nonneg _))
      (mul_nonneg (totalNuclearCharge_nonneg z)
        (integral_nonneg fun _ => abs_nonneg _))
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hbound] using hJ j hj

theorem tendsto_tfCoulombEnergy_self
    (f : ℕ → TFDensity) (σ : TFDensity)
    (hLp : Tendsto (fun j => (f j).val) atTop (𝓝 σ.val))
    (hL1 : Tendsto (fun j => ∫ x : Position, |(f j).val x - σ.val x|)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun j => tfCoulombEnergy (f j) (f j)) atTop
      (𝓝 (tfCoulombEnergy σ σ)) := by
  have hn : Tendsto (fun j => ‖(f j).val - σ.val‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hLp.sub_const σ.val).norm
  have hmδ : Tendsto (fun j => tfMass (tfDensityAbsDiff (f j) σ)) atTop (𝓝 0) := by
    simpa only [tfMass_tfDensityAbsDiff] using hL1
  have hmρ : Tendsto (fun j => tfMass (f j)) atTop (𝓝 (tfMass σ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at hL1
    obtain ⟨J, hJ⟩ := hL1 ε hε
    refine ⟨J, fun j hj => ?_⟩
    rw [Real.dist_eq]
    exact (abs_tfMass_sub_le (f j) σ).trans_lt (by
      have hnonneg : 0 ≤ ∫ x : Position, |(f j).val x - σ.val x| :=
        integral_nonneg fun _ => abs_nonneg _
      simpa only [tfMass_tfDensityAbsDiff, Real.dist_eq, sub_zero,
        abs_of_nonneg hnonneg] using hJ j hj)
  have hC : Tendsto (fun j =>
      (8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖(tfDensityAbsDiff (f j) σ).val‖ +
        tfMass (tfDensityAbsDiff (f j) σ)) atTop (𝓝 0) := by
    simp_rw [norm_tfDensityAbsDiff]
    simpa using (tendsto_const_nhds.mul hn).add hmδ
  have hmass : Tendsto (fun j =>
      tfMass (f j) + tfMass σ + tfMass (tfDensityAbsDiff (f j) σ)) atTop
      (𝓝 (tfMass σ + tfMass σ + 0)) :=
    (hmρ.add tendsto_const_nhds).add hmδ
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hprod : Tendsto (fun j =>
      ((8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖(tfDensityAbsDiff (f j) σ).val‖ +
          tfMass (tfDensityAbsDiff (f j) σ)) *
        (tfMass (f j) + tfMass σ + tfMass (tfDensityAbsDiff (f j) σ))) atTop
      (𝓝 0) := by simpa using hC.mul hmass
  rw [Metric.tendsto_atTop] at hprod
  obtain ⟨J, hJ⟩ := hprod ε hε
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq]
  exact (abs_tfCoulombEnergy_self_sub_le_norm_mass (f j) σ).trans_lt (by
    have hprod_nonneg : 0 ≤
        ((8 * Real.pi) ^ ((2 : ℝ) / 5) * ‖(tfDensityAbsDiff (f j) σ).val‖ +
            tfMass (tfDensityAbsDiff (f j) σ)) *
          (tfMass (f j) + tfMass σ + tfMass (tfDensityAbsDiff (f j) σ)) := by
      have hcoef : 0 ≤ (8 * Real.pi) ^ ((2 : ℝ) / 5) :=
        Real.rpow_nonneg (by positivity) _
      apply mul_nonneg
      · exact add_nonneg (mul_nonneg hcoef (norm_nonneg _))
          (tfMass_nonneg (tfDensityAbsDiff (f j) σ))
      · exact add_nonneg (add_nonneg (tfMass_nonneg (f j)) (tfMass_nonneg σ))
          (tfMass_nonneg (tfDensityAbsDiff (f j) σ))
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hprod_nonneg] using hJ j hj)

end LiebThirring.TFFunctional

end
