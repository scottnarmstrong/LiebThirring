/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeGeometry
public import LiebThirring.Assembly.Coulomb
import LiebThirring.Kinetic.DensityBasic

/-!
# Collision-free reference configurations in prescribed lattice cells

For every ordered cube assignment, this module chooses a collision-free point
of the corresponding product of cubes. Its Dirac mass supplies harmless
conditional probability data for sectors of zero probability.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring.TFSectors

/-- An interior point of the assigned cube, with a particle-dependent diagonal offset. -/
noncomputable def referenceParticlePosition {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) (i : Fin N) : Position :=
  WithLp.toLp 2 fun a =>
    ℓ * ((b i a : ℝ) + ((i : ℕ) + 1 : ℝ) / (N + 1 : ℝ))

/-- The ordered reference configuration associated with a cube assignment. -/
noncomputable def referenceConfiguration {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : Configuration N :=
  WithLp.toLp 2 fun ia => referenceParticlePosition ℓ b ia.1 ia.2

@[simp] theorem particlePosition_referenceConfiguration {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) (i : Fin N) :
    particlePosition (referenceConfiguration ℓ b) i = referenceParticlePosition ℓ b i := by
  rfl

theorem referenceParticlePosition_mem_latticeCell {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) (i : Fin N) :
    referenceParticlePosition ℓ b i ∈ latticeCell ℓ (b i) := by
  intro a
  change ℓ * (b i a : ℝ) ≤
      ℓ * ((b i a : ℝ) + ((i : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) ∧
    ℓ * ((b i a : ℝ) + ((i : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) <
      ℓ * ((b i a : ℝ) + 1)
  have hnum : 0 < (i : ℝ) + 1 := by positivity
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hfrac_pos : 0 < ((i : ℝ) + 1) / ((N : ℝ) + 1) :=
    div_pos hnum hden
  have hi : (i : ℕ) < N := i.isLt
  have hfrac_lt : ((i : ℝ) + 1) / ((N : ℝ) + 1) < 1 := by
    rw [div_lt_one hden]
    exact_mod_cast Nat.succ_lt_succ hi
  constructor
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hfrac_pos.le) hℓ.le
  · apply mul_lt_mul_of_pos_left _ hℓ
    linarith only [hfrac_lt]

theorem referenceParticlePosition_mem_latticeClosedCell {N : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) (i : Fin N) :
    referenceParticlePosition ℓ b i ∈ latticeClosedCell ℓ (b i) :=
  latticeCell_subset_closedCell ℓ (b i)
    (referenceParticlePosition_mem_latticeCell hℓ b i)

theorem referenceParticlePosition_ne {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) {i j : Fin N} (hij : i ≠ j) :
    referenceParticlePosition ℓ b i ≠ referenceParticlePosition ℓ b j := by
  intro heq
  have hbi : latticeLabel ℓ (referenceParticlePosition ℓ b i) = b i :=
    latticeLabel_eq_of_mem hℓ (referenceParticlePosition_mem_latticeCell hℓ b i)
  have hbj : latticeLabel ℓ (referenceParticlePosition ℓ b j) = b j :=
    latticeLabel_eq_of_mem hℓ (referenceParticlePosition_mem_latticeCell hℓ b j)
  have hb : b i = b j := hbi.symm.trans ((congrArg (latticeLabel ℓ) heq).trans hbj)
  have hc := congrArg (fun x : Position => x (0 : Fin 3)) heq
  change ℓ * ((b i 0 : ℝ) + ((i : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) =
    ℓ * ((b j 0 : ℝ) + ((j : ℕ) + 1 : ℝ) / (N + 1 : ℝ)) at hc
  rw [hb] at hc
  have hcast : (i : ℕ) = (j : ℕ) := by
    have hden : (0 : ℝ) < (N + 1 : ℝ) := by positivity
    have hadd := mul_left_cancel₀ hℓ.ne' hc
    have hfrac : ((i : ℝ) + 1) / ((N : ℝ) + 1) =
        ((j : ℝ) + 1) / ((N : ℝ) + 1) := add_left_cancel hadd
    have hreal : (i : ℝ) + 1 = (j : ℝ) + 1 :=
      (div_left_inj' hden.ne').mp hfrac
    exact_mod_cast (add_right_cancel hreal)
  exact hij (Fin.ext hcast)

theorem referenceConfiguration_collision_free {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) :
    ∀ i j, i ≠ j →
      particlePosition (referenceConfiguration ℓ b) i ≠
        particlePosition (referenceConfiguration ℓ b) j := by
  intro i j hij
  simpa only [particlePosition_referenceConfiguration] using
    referenceParticlePosition_ne hℓ b hij

theorem electronRepulsion_referenceConfiguration_ne_top {N : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) :
    electronRepulsion (referenceConfiguration ℓ b) ≠ ⊤ := by
  unfold electronRepulsion
  rw [ENNReal.sum_ne_top]
  intro i _
  rw [ENNReal.sum_ne_top]
  intro j hj
  rw [Assembly.coulombKernel_eq_of_ne
    (referenceConfiguration_collision_free hℓ b i j
      (ne_of_lt (Finset.mem_filter.mp hj).2))]
  exact ENNReal.ofReal_ne_top

/-- Dirac probability measure used to fill conditional data on a null sector. -/
noncomputable def referenceSectorMeasure {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : Measure (Configuration N) :=
  Measure.dirac (referenceConfiguration ℓ b)

instance referenceSectorMeasure_isProbabilityMeasure {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : IsProbabilityMeasure (referenceSectorMeasure ℓ b) := by
  unfold referenceSectorMeasure
  infer_instance

theorem referenceSectorMeasure_ae_mem_closedCell {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : Fin N → LatticeIndex) :
    ∀ᵐ x ∂referenceSectorMeasure ℓ b,
      ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i) := by
  unfold referenceSectorMeasure
  apply (ae_dirac_iff ?_).2
  intro i
  rw [particlePosition_referenceConfiguration]
  exact referenceParticlePosition_mem_latticeClosedCell hℓ b i
  have hm : MeasurableSet (⋂ i,
      (particlePosition · i) ⁻¹' latticeClosedCell ℓ (b i)) :=
    MeasurableSet.iInter fun i =>
      (measurableSet_latticeClosedCell ℓ (b i)).preimage (measurable_particlePosition i)
  convert hm using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]

theorem lintegral_electronRepulsion_referenceSectorMeasure {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) :
    (∫⁻ x, electronRepulsion x ∂referenceSectorMeasure ℓ b) =
      electronRepulsion (referenceConfiguration ℓ b) := by
  rw [referenceSectorMeasure, lintegral_dirac]

theorem lintegral_electronRepulsion_referenceSectorMeasure_ne_top {N : ℕ} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (b : Fin N → LatticeIndex) :
    (∫⁻ x, electronRepulsion x ∂referenceSectorMeasure ℓ b) ≠ ⊤ := by
  rw [lintegral_electronRepulsion_referenceSectorMeasure]
  exact electronRepulsion_referenceConfiguration_ne_top hℓ b

end LiebThirring.TFSectors

end
