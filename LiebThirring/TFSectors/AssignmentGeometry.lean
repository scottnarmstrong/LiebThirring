/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeGeometry
import LiebThirring.Kinetic.DensityBasic

/-!
# Ordered lattice-assignment sectors

The half-open lattice convention gives a measurable, pairwise disjoint, exact
partition of configuration space by the ordered cube labels of the particles.
This is the geometric part of the Neumann sector estimate.
-/

@[expose] public section

open Set MeasureTheory Function

namespace LiebThirring.TFSectors

/-- Ordered assignment of a configuration to prescribed half-open lattice cells. -/
def assignmentCell {N : ℕ} (ℓ : ℝ) (b : Fin N → LatticeIndex) :
    Set (Configuration N) :=
  {x | ∀ i, particlePosition x i ∈ latticeCell ℓ (b i)}

/-- Interior version of an ordered assignment cell. -/
def openAssignmentCell {N : ℕ} (ℓ : ℝ) (b : Fin N → LatticeIndex) :
    Set (Configuration N) :=
  {x | ∀ i a, ℓ * (b i a : ℝ) < particlePosition x i a ∧
    particlePosition x i a < ℓ * ((b i a : ℝ) + 1)}

/-- The ordered lattice label of every particle in a configuration. -/
noncomputable def assignmentLabel {N : ℕ} (ℓ : ℝ) (x : Configuration N) :
    Fin N → LatticeIndex :=
  fun i => latticeLabel ℓ (particlePosition x i)

theorem isOpen_openAssignmentCell {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : IsOpen (openAssignmentCell ℓ b) := by
  have heq : openAssignmentCell ℓ b = ⋂ i, ⋂ a,
      (fun x : Configuration N => particlePosition x i a) ⁻¹'
        Set.Ioo (ℓ * (b i a : ℝ)) (ℓ * ((b i a : ℝ) + 1)) := by
    ext x
    simp only [openAssignmentCell, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Ioo]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro a
  apply IsOpen.preimage ?_ isOpen_Ioo
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) a).comp
    ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_pi (fun c => PiLp.continuous_apply 2
        (fun _ : Fin N × Fin 3 => ℝ) (i, c))))

/-- Replacing every half-open coordinate interval by its interior changes an
assignment cell only on a Lebesgue-null set. -/
theorem openAssignmentCell_ae_eq_assignmentCell {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) :
    openAssignmentCell ℓ b =ᵐ[(volume : Measure (Configuration N))]
      assignmentCell ℓ b := by
  let lo : Fin N × Fin 3 → ℝ := fun ia => ℓ * (b ia.1 ia.2 : ℝ)
  let hi : Fin N × Fin 3 → ℝ := fun ia => ℓ * ((b ia.1 ia.2 : ℝ) + 1)
  have hpi : (Set.pi Set.univ fun ia => Set.Ioo (lo ia) (hi ia))
      =ᵐ[(volume : Measure (Fin N × Fin 3 → ℝ))]
        (Set.pi Set.univ fun ia => Set.Ico (lo ia) (hi ia)) :=
    Measure.pi_Ioo_ae_eq_pi_Icc.trans Measure.pi_Ico_ae_eq_pi_Icc.symm
  have hpull := (PiLp.volume_preserving_ofLp (Fin N × Fin 3)).quasiMeasurePreserving.ae hpi
  filter_upwards [hpull] with x hx
  simpa only [openAssignmentCell, assignmentCell, latticeCell, Set.mem_ofPred_eq, Set.mem_pi,
    Set.mem_univ, forall_const, Set.mem_Ioo, Set.mem_Ico, lo, hi,
    particlePosition, PiLp.toLp_apply, Prod.forall] using hx

theorem measurableSet_assignmentCell {N : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) : MeasurableSet (assignmentCell ℓ b) := by
  have heq : assignmentCell ℓ b =
      ⋂ i, (fun x : Configuration N => particlePosition x i) ⁻¹' latticeCell ℓ (b i) := by
    ext x
    simp only [assignmentCell, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_latticeCell ℓ (b i)).preimage (measurable_particlePosition i)

theorem mem_assignmentCell_assignmentLabel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : Configuration N) : x ∈ assignmentCell ℓ (assignmentLabel ℓ x) := by
  intro i
  exact mem_latticeCell_label hℓ (particlePosition x i)

theorem assignmentLabel_eq_of_mem {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : Fin N → LatticeIndex} {x : Configuration N}
    (hx : x ∈ assignmentCell ℓ b) : assignmentLabel ℓ x = b := by
  funext i
  exact latticeLabel_eq_of_mem hℓ (hx i)

theorem assignmentCell_disjoint {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b c : Fin N → LatticeIndex} (hbc : b ≠ c) :
    Disjoint (assignmentCell ℓ b) (assignmentCell ℓ c) := by
  apply disjoint_left.mpr
  intro x hxb hxc
  exact hbc ((assignmentLabel_eq_of_mem hℓ hxb).symm.trans
    (assignmentLabel_eq_of_mem hℓ hxc))

theorem iUnion_assignmentCell {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (⋃ b : Fin N → LatticeIndex, assignmentCell ℓ b) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨assignmentLabel ℓ x, mem_assignmentCell_assignmentLabel hℓ x⟩

end LiebThirring.TFSectors

end
