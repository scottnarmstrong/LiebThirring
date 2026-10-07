/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.RegularDiscrete
public import LiebThirring.TFCoulomb.SectorPairs
public import LiebThirring.TFFunctional.TrialDensities
public import LiebThirring.TFUpper.CubeStep

/-! # Step densities associated with cube occupations

The density attached to an ordered cube assignment is the literal finite sum
of its particle-cell indicators. Its pointwise value is the occupation count
of the unique half-open cube containing the point, divided by `alpha * ell^3`.
This is the step density used in Neumann sector estimates and regular-potential lower bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace LiebThirring.TFSectors

/-- The literal occupation-count step function. -/
noncomputable def sectorStepFunction {N : ℕ} (α ℓ : ℝ)
    (b : Fin N → LatticeIndex) (x : Position) : ℝ :=
  (TFCoulomb.sectorCount b (latticeLabel ℓ x) : ℝ) / (α * ℓ ^ 3)

theorem sectorStepFunction_eq_sum_indicators {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (α : ℝ) (b : Fin N → LatticeIndex) (x : Position) :
    sectorStepFunction α ℓ b x =
      ∑ i : Fin N, (latticeCell ℓ (b i)).indicator
        (fun _ => (α * ℓ ^ 3)⁻¹) x := by
  classical
  have hm (i : Fin N) : x ∈ latticeCell ℓ (b i) ↔ b i = latticeLabel ℓ x := by
    constructor
    · intro hx
      exact (latticeLabel_eq_of_mem hℓ hx).symm
    · intro hi
      rw [hi]
      exact mem_latticeCell_label hℓ x
  unfold sectorStepFunction TFCoulomb.sectorCount
  rw [div_eq_mul_inv, ← Finset.sum_boole
    (fun i : Fin N => b i = latticeLabel ℓ x) Finset.univ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b i = latticeLabel ℓ x
  · rw [ite_eq_left hi, indicator_of_mem (hm i |>.mpr hi)]
    simp
  · rw [ite_eq_right hi, indicator_of_notMem (not_congr (hm i) |>.mpr hi)]
    simp

theorem integrable_sectorStepFunction {N : ℕ} {α ℓ : ℝ}
    (_hα : 0 < α) (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) :
    Integrable (sectorStepFunction α ℓ b) := by
  rw [show sectorStepFunction α ℓ b = fun x => ∑ i : Fin N,
    (latticeCell ℓ (b i)).indicator (fun _ => (α * ℓ ^ 3)⁻¹) x by
      funext x; exact sectorStepFunction_eq_sum_indicators hℓ α b x]
  apply integrable_finsetSum
  intro i _
  apply (integrableOn_const (by
    rw [volume_latticeCell hℓ.le]
    exact ENNReal.ofReal_ne_top)).integrable_indicator
  exact measurableSet_latticeCell _ _

theorem memLp_sectorStepFunction {N : ℕ} {α ℓ : ℝ}
    (_hα : 0 < α) (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) :
    MemLp (sectorStepFunction α ℓ b) ((5 : ℝ≥0∞) / 3) volume := by
  rw [show sectorStepFunction α ℓ b = fun x => ∑ i : Fin N,
    (latticeCell ℓ (b i)).indicator (fun _ => (α * ℓ ^ 3)⁻¹) x by
      funext x; exact sectorStepFunction_eq_sum_indicators hℓ α b x]
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const _ (measurableSet_latticeCell ℓ (b i)) _
    (Or.inr (by rw [volume_latticeCell hℓ.le]; exact ENNReal.ofReal_ne_top))

/-- The Thomas--Fermi density belonging to an ordered cube assignment. -/
noncomputable def sectorStepDensity {N : ℕ} (α ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) : TFDensity :=
  TFFunctional.tfDensityOfFunction (sectorStepFunction α ℓ b)
    (memLp_sectorStepFunction α.property ℓ.property b)
    (Filter.Eventually.of_forall fun _x => div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg α.property.le (pow_nonneg ℓ.property.le 3)))
    (integrable_sectorStepFunction α.property ℓ.property b)

theorem sectorStepDensity_coeFn {N : ℕ} (α ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) :
    (sectorStepDensity α ℓ b).val =ᵐ[volume] sectorStepFunction α ℓ b :=
  TFFunctional.tfDensityOfFunction_coeFn _ _ _ _

theorem integral_latticeCell_constant {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (β : LatticeIndex) :
    (∫ x : Position, (latticeCell ℓ β).indicator (fun _ => c) x) = ℓ ^ 3 * c := by
  rw [integral_indicator_const _ (measurableSet_latticeCell _ _), measureReal_def,
    volume_latticeCell hℓ.le, ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3), smul_eq_mul]

/-- The sector step density has exactly the particle number divided by the scaling. -/
theorem tfMass_sectorStepDensity {N : ℕ} (α ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) :
    tfMass (sectorStepDensity α ℓ b) = (N : ℝ) / α := by
  rw [tfMass, integral_congr_ae (sectorStepDensity_coeFn α ℓ b)]
  have heq : sectorStepFunction α ℓ b = fun x => ∑ i : Fin N,
      (latticeCell ℓ (b i)).indicator (fun _ => (α.val * ℓ.val ^ 3)⁻¹) x := by
    funext x
    exact sectorStepFunction_eq_sum_indicators ℓ.property α b x
  rw [heq, integral_finsetSum _]
  · simp only [integral_latticeCell_constant ℓ.property, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [α.property.ne', ℓ.property.ne']
  · intro i _
    apply (integrableOn_const (by
      rw [volume_latticeCell ℓ.property.le]
      exact ENNReal.ofReal_ne_top)).integrable_indicator
    exact measurableSet_latticeCell _ _

/-- Under the exact scaling relation, every sector step density has mass `nu`. -/
theorem tfMass_sectorStepDensity_eq {N : ℕ} (α ℓ : {x : ℝ // 0 < x})
    (ν : ℝ) (hN : (N : ℝ) = α * ν) (b : Fin N → LatticeIndex) :
    tfMass (sectorStepDensity α ℓ b) = ν := by
  rw [tfMass_sectorStepDensity, hN]
  exact mul_div_cancel_left₀ ν α.property.ne'

theorem sectorStepFunction_eq_occupied_sum {N : ℕ} {α ℓ : ℝ}
    (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) (x : Position) :
    sectorStepFunction α ℓ b x =
      ∑ β ∈ TFCoulomb.occupiedCubes b, (latticeCell ℓ β).indicator
        (fun _ => (TFCoulomb.sectorCount b β : ℝ) / (α * ℓ ^ 3)) x := by
  classical
  let βx := latticeLabel ℓ x
  by_cases hβ : βx ∈ TFCoulomb.occupiedCubes b
  · rw [Finset.sum_eq_single βx]
    · rw [indicator_of_mem (mem_latticeCell_label hℓ x)]
      rfl
    · intro γ hγ hne
      rw [indicator_of_notMem]
      intro hx
      exact hne (latticeLabel_eq_of_mem hℓ hx).symm
    · exact fun hn => False.elim (hn hβ)
  · have hc : TFCoulomb.sectorCount b βx = 0 := by
      unfold TFCoulomb.sectorCount
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro i _ hi
      exact hβ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [sectorStepFunction, hc, Nat.cast_zero, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro γ hγ
    rw [indicator_of_notMem]
    intro hx
    apply hβ
    have heq : γ = βx := (latticeLabel_eq_of_mem hℓ hx).symm
    rwa [← heq]

theorem sectorStepFunction_rpow {N : ℕ} {α ℓ : ℝ}
    (_hα : 0 < α) (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) (x : Position) :
    sectorStepFunction α ℓ b x ^ ((5 : ℝ) / 3) =
      ∑ β ∈ TFCoulomb.occupiedCubes b, (latticeCell ℓ β).indicator
        (fun _ => ((TFCoulomb.sectorCount b β : ℝ) / (α * ℓ ^ 3)) ^
          ((5 : ℝ) / 3)) x := by
  classical
  rw [sectorStepFunction_eq_occupied_sum hℓ]
  by_cases hx : ∃ β ∈ TFCoulomb.occupiedCubes b, x ∈ latticeCell ℓ β
  · obtain ⟨β, hβ, hx⟩ := hx
    have hz (γ : LatticeIndex) (hγ : γ ≠ β) : x ∉ latticeCell ℓ γ := by
      intro hxγ
      exact hγ ((latticeLabel_eq_of_mem hℓ hxγ).symm.trans
        (latticeLabel_eq_of_mem hℓ hx))
    rw [Finset.sum_eq_single β, Finset.sum_eq_single β]
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · intro γ hγ hne
      exact indicator_of_notMem (hz γ hne) _
    · exact fun hn => False.elim (hn hβ)
    · intro γ hγ hne
      exact indicator_of_notMem (hz γ hne) _
    · exact fun hn => False.elim (hn hβ)
  · have hz (β : LatticeIndex) (hβ : β ∈ TFCoulomb.occupiedCubes b) :
        x ∉ latticeCell ℓ β := fun hmem => hx ⟨β, hβ, hmem⟩
    rw [Finset.sum_eq_zero (fun β hβ => indicator_of_notMem (hz β hβ) _),
      Finset.sum_eq_zero (fun β hβ => indicator_of_notMem (hz β hβ) _),
      Real.zero_rpow (by norm_num : (5 / 3 : ℝ) ≠ 0)]

/-- Exact `L^(5/3)` moment of an occupation step density. -/
theorem integral_sectorStepDensity_rpow {N : ℕ} (α ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) :
    (∫ x : Position, ((sectorStepDensity α ℓ b).val x) ^ ((5 : ℝ) / 3)) =
      ℓ.val⁻¹ ^ 2 * α.val ^ (-(5 : ℝ) / 3) *
        ∑ β ∈ TFCoulomb.occupiedCubes b,
          (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3) := by
  have heq : (fun x : Position => ((sectorStepDensity α ℓ b).val x) ^
      ((5 : ℝ) / 3)) =ᵐ[volume] fun x =>
      ∑ β ∈ TFCoulomb.occupiedCubes b, (latticeCell ℓ β).indicator
        (fun _ => ((TFCoulomb.sectorCount b β : ℝ) / (α * ℓ ^ 3)) ^
          ((5 : ℝ) / 3)) x := by
    filter_upwards [sectorStepDensity_coeFn α ℓ b] with x hx
    rw [hx, sectorStepFunction_rpow α.property ℓ.property]
  rw [integral_congr_ae heq, integral_finsetSum _]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [integral_latticeCell_constant ℓ.property]
    have hn : 0 ≤ (TFCoulomb.sectorCount b β : ℝ) / α :=
      div_nonneg (Nat.cast_nonneg _) α.property.le
    rw [show (TFCoulomb.sectorCount b β : ℝ) / (α.val * ℓ.val ^ 3) =
        ((TFCoulomb.sectorCount b β : ℝ) / α.val) / ℓ.val ^ 3 by ring,
      TFUpper.cube_kinetic_moment_factor ℓ.val
        ((TFCoulomb.sectorCount b β : ℝ) / α.val) ℓ.property hn,
      Real.div_rpow (Nat.cast_nonneg _) α.property.le]
    rw [show (-(5 : ℝ) / 3) = -((5 : ℝ) / 3) by ring,
      Real.rpow_neg α.property.le]
    field_simp [α.property.ne']
  · intro β _
    apply (integrableOn_const (by
      rw [volume_latticeCell ℓ.property.le]
      exact ENNReal.ofReal_ne_top)).integrable_indicator
    exact measurableSet_latticeCell _ _

/-- Every cube carries its occupation number divided by `alpha`. -/
theorem tfDensityMeasure_sectorStepDensity_latticeCell {N : ℕ}
    (α ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex) (β : LatticeIndex) :
    tfDensityMeasure (sectorStepDensity α ℓ b) (latticeCell ℓ β) =
      ENNReal.ofReal ((TFCoulomb.sectorCount b β : ℝ) / α) := by
  unfold tfDensityMeasure
  rw [withDensity_apply _ (measurableSet_latticeCell _ _)]
  have heq : (fun x : Position => ENNReal.ofReal ((sectorStepDensity α ℓ b).val x))
      =ᵐ[volume.restrict (latticeCell ℓ β)] fun _ =>
        ENNReal.ofReal ((TFCoulomb.sectorCount b β : ℝ) / (α * ℓ ^ 3)) := by
    filter_upwards [ae_restrict_mem (measurableSet_latticeCell ℓ β),
      (sectorStepDensity_coeFn α ℓ b).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hρ
    rw [hρ, sectorStepFunction, latticeLabel_eq_of_mem ℓ.property hx]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ,
    volume_latticeCell ℓ.property.le, mul_comm,
    ← ENNReal.ofReal_mul (pow_nonneg ℓ.property.le 3)]
  congr 1
  field_simp [α.property.ne', ℓ.property.ne']

/-- The boxwise constant attraction has the exact occupation-sum value. -/
theorem integral_boxCappedPotential_mul_sectorStepDensity {N M : ℕ}
    (α ℓ : {x : ℝ // 0 < x}) {δ : ℝ} (_hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (b : Fin N → LatticeIndex) :
    (∫ x : Position, TFCoulomb.boxCappedPotential δ ℓ z R x *
      (sectorStepDensity α ℓ b).val x) =
        α.val⁻¹ * ∑ i : Fin N,
          TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i) := by
  have heq : (fun x : Position => TFCoulomb.boxCappedPotential δ ℓ z R x *
      (sectorStepDensity α ℓ b).val x) =ᵐ[volume] fun x =>
        ∑ i : Fin N, (latticeCell ℓ (b i)).indicator
          (fun _ => TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i) *
            (α.val * ℓ.val ^ 3)⁻¹) x := by
    filter_upwards [sectorStepDensity_coeFn α ℓ b] with x hρ
    rw [hρ, sectorStepFunction_eq_sum_indicators ℓ.property, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ latticeCell ℓ (b i)
    · rw [indicator_of_mem hx, indicator_of_mem hx, TFCoulomb.boxCappedPotential,
        latticeLabel_eq_of_mem ℓ.property hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  rw [integral_congr_ae heq, integral_finsetSum _]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_latticeCell_constant ℓ.property]
    field_simp [α.property.ne', ℓ.property.ne']
  · intro i _
    apply (integrableOn_const (by
      rw [volume_latticeCell ℓ.property.le]
      exact ENNReal.ofReal_ne_top)).integrable_indicator
    exact measurableSet_latticeCell _ _


end LiebThirring.TFSectors

end
