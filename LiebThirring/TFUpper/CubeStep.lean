/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeGeometry
public import LiebThirring.TFFunctional.DensityBasic

/-! # Finite cube step densities in TF coordinates

The geometric data consists of a common side length, distinct lattice labels,
and nonnegative masses. `CubeMesh.represents` is the literal indicator formula,
not a package of estimates. Proof: step-density approximation/Slater upper bound, Lieb–Simon (1977) III.5, p. 72.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LiebThirring.TFUpper

/-- A finite collection of distinct cubes with their prescribed masses. -/
structure CubeMesh (B : ℕ) where
  side : {ℓ : ℝ // 0 < ℓ}
  label : Fin B → LatticeIndex
  distinct : Function.Injective label
  mass : Fin B → ℝ≥0

/-- The literal piecewise constant density, with each cube's integral equal to its mass. -/
noncomputable def CubeMesh.stepFunction {B : ℕ} (g : CubeMesh B) (x : Position) : ℝ :=
  ∑ b, (latticeCell g.side.val (g.label b)).indicator
    (fun _ => (g.mass b : ℝ) / g.side.val ^ 3) x

/-- The density agrees with the cube indicator formula a.e. -/
def CubeMesh.represents {B : ℕ} (g : CubeMesh B) (ρ : TFDensity) : Prop :=
  ∀ᵐ x : Position, ρ.val x = g.stepFunction x

theorem integrable_cube_constant {B : ℕ} (g : CubeMesh B) (b : Fin B) (c : ℝ) :
    Integrable ((latticeCell g.side.val (g.label b)).indicator (fun _ => c)) := by
  apply (integrableOn_const (by
    rw [volume_latticeCell g.side.property.le]
    exact ENNReal.ofReal_ne_top)).integrable_indicator
  exact measurableSet_latticeCell _ _

theorem integral_cube_constant {B : ℕ} (g : CubeMesh B) (b : Fin B) (c : ℝ) :
    (∫ x : Position, (latticeCell g.side.val (g.label b)).indicator (fun _ => c) x) =
      g.side.val ^ 3 * c := by
  rw [integral_indicator_const _ (measurableSet_latticeCell _ _), measureReal_def,
    volume_latticeCell g.side.property.le, ENNReal.toReal_ofReal (pow_nonneg g.side.property.le 3),
    smul_eq_mul]

theorem CubeMesh.integrable_stepFunction {B : ℕ} (g : CubeMesh B) :
    Integrable g.stepFunction := by
  apply integrable_finsetSum
  intro b _
  exact integrable_cube_constant g b _

theorem CubeMesh.mass_eq {B : ℕ} (g : CubeMesh B) (ρ : TFDensity)
    (hρ : g.represents ρ) : tfMass ρ = ∑ b, (g.mass b : ℝ) := by
  rw [tfMass, integral_congr_ae hρ]
  change (∫ x : Position, ∑ b, (latticeCell g.side.val (g.label b)).indicator
    (fun _ => (g.mass b : ℝ) / g.side.val ^ 3) x) = _
  rw [integral_finsetSum _ (fun b _ => integrable_cube_constant g b _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_cube_constant]
  exact mul_div_cancel₀ _ (pow_ne_zero 3 g.side.property.ne')

theorem CubeMesh.stepFunction_rpow {B : ℕ} (g : CubeMesh B) (x : Position) :
    g.stepFunction x ^ ((5 : ℝ) / 3) =
      ∑ b, (latticeCell g.side.val (g.label b)).indicator
        (fun _ => ((g.mass b : ℝ) / g.side.val ^ 3) ^ ((5 : ℝ) / 3)) x := by
  classical
  by_cases hx : ∃ b, x ∈ latticeCell g.side.val (g.label b)
  · obtain ⟨b, hb⟩ := hx
    have hz (a : Fin B) (hab : a ≠ b) : x ∉ latticeCell g.side.val (g.label a) := by
      intro ha
      exact hab (g.distinct ((latticeLabel_eq_of_mem g.side.property ha).symm.trans
        (latticeLabel_eq_of_mem g.side.property hb)))
    have hsum (f : Fin B → ℝ) :
        (∑ a, (latticeCell g.side.val (g.label a)).indicator (fun _ => f a) x) = f b := by
      rw [Finset.sum_eq_single b]
      · exact indicator_of_mem hb _
      · intro a _ hab
        exact indicator_of_notMem (hz a hab) _
      · intro hn
        exact False.elim (hn (Finset.mem_univ b))
    rw [CubeMesh.stepFunction, hsum, hsum]
  · have hz (b : Fin B) : x ∉ latticeCell g.side.val (g.label b) :=
      fun hb => hx ⟨b, hb⟩
    simp only [CubeMesh.stepFunction, indicator_of_notMem (hz _),
      Finset.sum_const_zero, Real.zero_rpow (by norm_num : (5 / 3 : ℝ) ≠ 0)]

theorem cube_kinetic_moment_factor (ℓ m : ℝ) (hℓ : 0 < ℓ) (hm : 0 ≤ m) :
    ℓ ^ 3 * (m / ℓ ^ 3) ^ ((5 : ℝ) / 3) = ℓ⁻¹ ^ 2 * m ^ ((5 : ℝ) / 3) := by
  rw [Real.div_rpow hm (pow_nonneg hℓ.le 3),
    ← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
  norm_num only [show (3 : ℝ) * (5 / 3 : ℝ) = 5 by norm_num, Real.rpow_ofNat]
  field_simp

theorem CubeMesh.kinetic_moment_eq {B : ℕ} (g : CubeMesh B) (ρ : TFDensity)
    (hρ : g.represents ρ) :
    (∫ x : Position, ρ.val x ^ ((5 : ℝ) / 3)) =
      g.side.val⁻¹ ^ 2 * ∑ b, (g.mass b : ℝ) ^ ((5 : ℝ) / 3) := by
  have heq : (fun x : Position => ρ.val x ^ ((5 : ℝ) / 3)) =ᵐ[volume]
      fun x => ∑ b, (latticeCell g.side.val (g.label b)).indicator
        (fun _ => ((g.mass b : ℝ) / g.side.val ^ 3) ^ ((5 : ℝ) / 3)) x := by
    filter_upwards [hρ] with x hx
    rw [hx, g.stepFunction_rpow]
  rw [integral_congr_ae heq,
    integral_finsetSum _ (fun b _ => integrable_cube_constant g b _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_cube_constant]
  exact cube_kinetic_moment_factor g.side.val (g.mass b) g.side.property (g.mass b).property

end LiebThirring.TFUpper
end
