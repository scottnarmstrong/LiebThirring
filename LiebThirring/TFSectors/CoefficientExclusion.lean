/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.SpectralInput
public import LiebThirring.Kinetic.Permutation
public import LiebThirring.TFCubes.RegionL2
public import LiebThirring.Kinetic.CurryingTransport

/-!
# Pauli coefficient exclusion in an assignment sector

A particle permutation preserving an ordered cube assignment acts isometrically
on the sector L² space. An antisymmetric vector is orthogonal to every test
vector fixed by a transposition. This is the coefficient-exclusion step of
it assumes no spectral or sector-energy lower bound.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace LiebThirring.TFSectors

theorem measurePreserving_permutePositions_restrict_openAssignmentCell {N : ℕ} {ℓ : ℝ}
    (b : Fin N → LatticeIndex) (σ : Equiv.Perm (Fin N))
    (hb : ∀ i, b (σ i) = b i) :
    MeasurePreserving (permutePositions σ)
      (volume.restrict (openAssignmentCell ℓ b))
      (volume.restrict (openAssignmentCell ℓ b)) := by
  have hpre : permutePositions σ ⁻¹' openAssignmentCell ℓ b = openAssignmentCell ℓ b := by
    ext x
    constructor
    · intro hx j
      have h := hx (σ.symm j)
      rw [particlePosition_permutePositions, σ.apply_symm_apply] at h
      have hb' : b (σ.symm j) = b j := by
        rw [← hb (σ.symm j), σ.apply_symm_apply]
      simpa only [hb'] using h
    · intro hx i
      rw [particlePosition_permutePositions]
      simpa only [hb i] using hx (σ i)
  have h := (measurePreserving_permutePositions σ).restrict_preimage
    (isOpen_openAssignmentCell ℓ b).measurableSet
  rw [hpre] at h
  exact h

/-- Simultaneous spatial and spin permutation on a local assignment sector. -/
noncomputable def assignmentPermutation {N q : ℕ} {ℓ : ℝ}
    (b : Fin N → LatticeIndex) (σ : Equiv.Perm (Fin N))
    (hb : ∀ i, b (σ i) = b i) :
    TFCubes.ConfigurationRegionState N q (openAssignmentCell ℓ b) →ₗᵢ[ℂ]
      TFCubes.ConfigurationRegionState N q (openAssignmentCell ℓ b) :=
  (l2TargetEquiv (volume.restrict (openAssignmentCell ℓ b))
      (spinPermutationLinearIsometryEquiv (q := q) σ)).toLinearIsometry.comp
    (Lp.compMeasurePreservingₗᵢ ℂ (permutePositions σ)
      (measurePreserving_permutePositions_restrict_openAssignmentCell b σ hb))

/-- The local permutation has its literal simultaneous position/spin representative. -/
theorem assignmentPermutation_apply_ae {N q : ℕ} {ℓ : ℝ}
    (b : Fin N → LatticeIndex) (σ : Equiv.Perm (Fin N))
    (hb : ∀ i, b (σ i) = b i)
    (u : TFCubes.ConfigurationRegionState N q (openAssignmentCell ℓ b)) :
    assignmentPermutation b σ hb u =ᵐ[volume.restrict (openAssignmentCell ℓ b)]
      fun x => spinPermutationLinearIsometryEquiv σ (u (permutePositions σ x)) := by
  filter_upwards [l2TargetEquiv_ae (volume.restrict (openAssignmentCell ℓ b))
      (spinPermutationLinearIsometryEquiv (q := q) σ)
      (Lp.compMeasurePreserving (permutePositions σ)
        (measurePreserving_permutePositions_restrict_openAssignmentCell b σ hb) u),
    Lp.coeFn_compMeasurePreserving u
      (measurePreserving_permutePositions_restrict_openAssignmentCell b σ hb)] with x hx hu
  change assignmentPermutation b σ hb u x = _ at hx
  rw [hx, hu]
  rfl

/-- An anti-invariant vector is orthogonal to every invariant test vector. -/
theorem inner_eq_zero_of_assignmentPermutation_eq_neg_of_eq_self
    {N q : ℕ} {ℓ : ℝ} (b : Fin N → LatticeIndex)
    (σ : Equiv.Perm (Fin N)) (hb : ∀ i, b (σ i) = b i)
    (u v : TFCubes.ConfigurationRegionState N q (openAssignmentCell ℓ b))
    (hu : assignmentPermutation b σ hb u = -u)
    (hv : assignmentPermutation b σ hb v = v) :
    ⟪v, u⟫_ℂ = 0 := by
  have h := (assignmentPermutation b σ hb).inner_map_map v u
  rw [hv, hu, inner_neg_right] at h
  have htwo : (2 : ℂ) * ⟪v, u⟫_ℂ = 0 := by
    calc
      (2 : ℂ) * ⟪v, u⟫_ℂ = ⟪v, u⟫_ℂ + ⟪v, u⟫_ℂ := by ring
      _ = 0 := add_eq_zero_iff_eq_neg.mpr h.symm
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Restriction of a global fermionic state is anti-invariant under a
transposition that preserves the ordered assignment. -/
theorem assignmentPermutation_regionRestrictL2_swap_eq_neg {N q : ℕ}
    (ψ : State N q) (hψ : antisymmetric ψ) (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) {i j : Fin N} (hij : i ≠ j) (hb : b i = b j) :
    assignmentPermutation b (Equiv.swap i j) (assignment_stable_swap b hb)
        (TFCubes.regionRestrictL2 volume (openAssignmentCell ℓ b) ψ) =
      -TFCubes.regionRestrictL2 volume (openAssignmentCell ℓ b) ψ := by
  let σ := Equiv.swap i j
  let hstable := assignment_stable_swap b hb
  let u := TFCubes.regionRestrictL2 volume (openAssignmentCell ℓ b) ψ
  have hmp := measurePreserving_permutePositions_restrict_openAssignmentCell (ℓ := ℓ.val) b σ hstable
  have hu := TFCubes.regionRestrictL2_ae volume (openAssignmentCell ℓ b) ψ
  have hanti : ∀ᵐ x ∂volume.restrict (openAssignmentCell ℓ b),
      ∀ s : SpinLabels N q,
        ψ (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ψ x s :=
    ae_restrict_of_ae (hψ σ)
  apply Lp.ext
  filter_upwards [assignmentPermutation_apply_ae b σ hstable u,
    hu, hmp.quasiMeasurePreserving.ae hu, hanti, Lp.coeFn_neg u] with x hperm hux hupx ha hneg
  rw [hperm, hneg]
  apply PiLp.ext
  intro s
  change u (permutePositions σ x) (permuteSpins σ s) = -u x s
  rw [hupx, hux, ha s]
  simp [σ, Equiv.Perm.sign_swap hij]

/-- A literal product-basis vector is invariant when the exchanged particles
have the same cube and the same spatial-and-spin mode label. -/
theorem assignmentPermutation_productBasis_swap_eq_self {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (data : NeumannProductSpectralData N q ℓ b)
    (k : Fin N → TFLattice.ModeIndex q) {i j : Fin N}
    (hb : b i = b j) (hk : k i = k j) :
    assignmentPermutation b (Equiv.swap i j) (assignment_stable_swap b hb) (data.basis k) =
      data.basis k := by
  let σ := Equiv.swap i j
  let hstable := assignment_stable_swap b hb
  have hmp := measurePreserving_permutePositions_restrict_openAssignmentCell (ℓ := ℓ.val) b σ hstable
  have hmode := data.basis_ae k
  apply Lp.ext
  filter_upwards [assignmentPermutation_apply_ae b σ hstable (data.basis k),
    hmode, hmp.quasiMeasurePreserving.ae hmode] with x hperm hx hpx
  rw [hperm, hx]
  apply PiLp.ext
  intro s
  change data.basis k (permutePositions σ x) (permuteSpins σ s) =
    neumannProductMode ℓ b k x s
  rw [hpx]
  exact neumannProductMode_swap ℓ b k hb hk x s

/-- Pauli exclusion for one repeated product-mode label in a cube. -/
theorem neumannProductBasis_repr_eq_zero_of_repeated_pair {N q : ℕ}
    (ψ : State N q) (hψ : antisymmetric ψ) (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (data : NeumannProductSpectralData N q ℓ b)
    (k : Fin N → TFLattice.ModeIndex q) {i j : Fin N}
    (hij : i ≠ j) (hb : b i = b j) (hk : k i = k j) :
    data.basis.repr (TFCubes.regionRestrictL2 volume (openAssignmentCell ℓ b) ψ) k = 0 := by
  rw [HilbertBasis.repr_apply_apply]
  exact inner_eq_zero_of_assignmentPermutation_eq_neg_of_eq_self b (Equiv.swap i j)
    (assignment_stable_swap b hb) _ _
    (assignmentPermutation_regionRestrictL2_swap_eq_neg ψ hψ ℓ b hij hb)
    (assignmentPermutation_productBasis_swap_eq_self ℓ b data k hb hk)

/-- Every coefficient whose product label violates within-cube distinctness vanishes. -/
theorem neumannProductBasis_repr_eq_zero_of_not_distinctWithinCubes {N q : ℕ}
    (ψ : State N q) (hψ : antisymmetric ψ) (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (data : NeumannProductSpectralData N q ℓ b)
    (k : Fin N → TFLattice.ModeIndex q) (hk : ¬ DistinctWithinCubes b k) :
    data.basis.repr (TFCubes.regionRestrictL2 volume (openAssignmentCell ℓ b) ψ) k = 0 := by
  classical
  simp only [DistinctWithinCubes, not_forall] at hk
  obtain ⟨i, j, hb, hmode, hij⟩ := hk
  exact neumannProductBasis_repr_eq_zero_of_repeated_pair ψ hψ ℓ b data k hij hb hmode

end LiebThirring.TFSectors

end
