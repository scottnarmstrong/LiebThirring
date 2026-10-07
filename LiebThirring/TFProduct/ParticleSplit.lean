/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.WeakTransport
public import LiebThirring.TFSectors.AssignmentGeometry
public import LiebThirring.TFCubes.CubeModes

/-! # Splitting off one selected particle -/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.TFProduct

open LiebThirring TFCubes TFSectors Sobolev

noncomputable section

/-- Reindex the complement of `i: Fin (n+1)` by `Fin n`. -/
def residualConfigurationEquiv {n : ℕ} (i : Fin (n + 1)) :
    Configuration n ≃ₗᵢ[ℝ] OtherConfiguration i :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((finSuccAboveEquiv i).prodCongr (Equiv.refl (Fin 3)))

@[simp] theorem residualConfigurationEquiv_apply {n : ℕ} (i : Fin (n + 1))
    (y : Configuration n) (j : Fin n) (a : Fin 3) :
    residualConfigurationEquiv i y
      (⟨i.succAbove j, i.succAbove_ne j⟩, a) = y (j, a) := by
  change y ((finSuccAboveEquiv i).symm
    ⟨i.succAbove j, i.succAbove_ne j⟩, a) = y (j, a)
  have he : (⟨i.succAbove j, i.succAbove_ne j⟩ :
      {r : Fin (n + 1) // r ≠ i}) = finSuccAboveEquiv i j := by
    ext
    rfl
  rw [he, Equiv.symm_apply_apply]

/-- Continuous linear coordinates consisting of particle `i` followed by the
remaining particles in `succAbove` order. -/
def particleSplitEquiv {n : ℕ} (i : Fin (n + 1)) :
    (Position × Configuration n) ≃L[ℝ] Configuration (n + 1) :=
  ((ContinuousLinearEquiv.refl ℝ Position).prodCongr
      (residualConfigurationEquiv i).toContinuousLinearEquiv).trans
    (insertionContinuousLinearEquiv i)

@[simp] theorem particleSplitEquiv_apply {n : ℕ} (i : Fin (n + 1))
    (z : Position × Configuration n) :
    particleSplitEquiv i z = insertParticle i z.1 (residualConfigurationEquiv i z.2) := by
  change insertionContinuousLinearEquiv i
    (z.1, residualConfigurationEquiv i z.2) = _
  rw [insertionContinuousLinearEquiv_apply]

@[simp] theorem particlePosition_particleSplit_self {n : ℕ} (i : Fin (n + 1))
    (z : Position × Configuration n) :
    particlePosition (particleSplitEquiv i z) i = z.1 := by
  rw [particleSplitEquiv_apply, particlePosition_insertParticle]

@[simp] theorem particlePosition_particleSplit_succAbove {n : ℕ} (i : Fin (n + 1))
    (z : Position × Configuration n) (j : Fin n) :
    particlePosition (particleSplitEquiv i z) (i.succAbove j) = particlePosition z.2 j := by
  ext a
  simp only [particleSplitEquiv_apply, particlePosition, insertParticle, PiLp.toLp_apply]
  rw [dite_eq_right (i.succAbove_ne j)]
  exact residualConfigurationEquiv_apply i z.2 j a

/-- The selected-particle split preserves the corresponding Lebesgue volumes. -/
theorem measurePreserving_particleSplitEquiv {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (particleSplitEquiv i) volume volume := by
  have hr : MeasurePreserving (residualConfigurationEquiv i) volume volume :=
    (residualConfigurationEquiv i).measurePreserving
  have hp : MeasurePreserving
      (fun z : Position × Configuration n => (z.1, residualConfigurationEquiv i z.2))
      volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact MeasurePreserving.prod (MeasurePreserving.id (volume : Measure Position)) hr
  exact (measurePreserving_insertionContinuousLinearEquiv i).comp hp

/-- Splitting particle `i` turns its open assignment cell into the product of
its physical cube and the residual open assignment cell. -/
theorem particleSplitEquiv_preimage_openAssignmentCell {n : ℕ}
    (i : Fin (n + 1)) (ℓ : {x : ℝ // 0 < x})
    (b : Fin (n + 1) → LatticeIndex) :
    particleSplitEquiv i ⁻¹' openAssignmentCell ℓ.val b =
      cubeInterior (latticeCorner ℓ.val (b i)) ℓ ×ˢ
        openAssignmentCell ℓ.val (fun j => b (i.succAbove j)) := by
  ext z
  change (∀ j a, ℓ.val * (b j a : ℝ) < particlePosition (particleSplitEquiv i z) j a ∧
      particlePosition (particleSplitEquiv i z) j a < ℓ.val * ((b j a : ℝ) + 1)) ↔
    ((∀ a, latticeCorner ℓ.val (b i) a < z.1 a ∧
        z.1 a < latticeCorner ℓ.val (b i) a + ℓ.val) ∧
      ∀ j a, ℓ.val * (b (i.succAbove j) a : ℝ) < particlePosition z.2 j a ∧
        particlePosition z.2 j a < ℓ.val * ((b (i.succAbove j) a : ℝ) + 1))
  constructor
  · intro h
    constructor
    · intro a
      have ha := h i a
      rw [particlePosition_particleSplit_self] at ha
      constructor
      · simpa only [latticeCorner, PiLp.toLp_apply] using ha.1
      · simpa only [latticeCorner, PiLp.toLp_apply, mul_add, mul_one] using ha.2
    · intro j a
      have ha := h (i.succAbove j) a
      rwa [particlePosition_particleSplit_succAbove] at ha
  · rintro ⟨hi, hr⟩ j a
    by_cases hj : j = i
    · subst j
      have ha := hi a
      rw [particlePosition_particleSplit_self]
      constructor
      · simpa only [latticeCorner, PiLp.toLp_apply] using ha.1
      · simpa only [latticeCorner, PiLp.toLp_apply, mul_add, mul_one] using ha.2
    · let r : {j : Fin (n + 1) // j ≠ i} := ⟨j, hj⟩
      let k : Fin n := (finSuccAboveEquiv i).symm r
      have hk : i.succAbove k = j := by
        have he := (finSuccAboveEquiv i).apply_symm_apply r
        exact congrArg Subtype.val he
      rw [← hk, particlePosition_particleSplit_succAbove]
      exact hr k a

/-- The restricted selected-particle split is measure preserving onto the
product of the selected cube and residual assignment cell. -/
theorem measurePreserving_particleSplitEquiv_restrict {n : ℕ}
    (i : Fin (n + 1)) (ℓ : {x : ℝ // 0 < x})
    (b : Fin (n + 1) → LatticeIndex) :
    MeasurePreserving (particleSplitEquiv i)
      (volume.restrict
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ ×ˢ
          openAssignmentCell ℓ.val (fun j => b (i.succAbove j))))
      (volume.restrict (openAssignmentCell ℓ.val b)) := by
  have hΩ : MeasurableSet (openAssignmentCell ℓ.val b) :=
    (isOpen_openAssignmentCell ℓ.val b).measurableSet
  have h := (measurePreserving_particleSplitEquiv i).restrict_preimage hΩ
  rw [particleSplitEquiv_preimage_openAssignmentCell i ℓ b] at h
  exact h

/-- The selected coordinate vector splits into its spatial basis vector and a
zero residual configuration. -/
theorem particleSplitEquiv_symm_coordinateVector_self {n : ℕ}
    (i : Fin (n + 1)) (a : Fin 3) :
    (particleSplitEquiv i).symm (coordinateVector (i, a)) =
      (EuclideanSpace.basisFun (Fin 3) ℝ a, (0 : Configuration n)) := by
  apply (particleSplitEquiv i).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext ja
  by_cases hji : ja.1 = i
  · simp [particleSplitEquiv_apply, insertParticle, coordinateVector,
      EuclideanSpace.basisFun_apply, hji, Prod.ext_iff]
  · simp [particleSplitEquiv_apply, insertParticle, coordinateVector,
      residualConfigurationEquiv, EuclideanSpace.basisFun_apply, hji,
      Prod.ext_iff]

end

end LiebThirring.TFProduct

end
