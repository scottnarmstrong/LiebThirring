/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.AssignmentGeometry
public import LiebThirring.TFCubes.CubeCoordinates
public import LiebThirring.Kinetic.DensityBasic

/-! # Product measure coordinates for assignment cells

The flat Euclidean configuration measure is transported to the finite product
of the physical one-particle measures.  Restriction then identifies an open
assignment cell with the product of its open cubes.
-/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.TFProduct

open LiebThirring TFCubes TFSectors

noncomputable section

private theorem measurePreserving_curry_pi
    {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry I J X)
      (Measure.pi fun ij : I × J => μ ij.1 ij.2)
      (Measure.pi fun i : I => Measure.pi fun j : J => μ i j) := by
  classical
  let C : I → Set (Set (J → X)) := fun _ =>
    {s | ∃ t : J → Set X, (∀ j, MeasurableSet (t j)) ∧ s = Set.pi Set.univ t}
  have hC_generate (i : I) : MeasurableSpace.generateFrom (C i) =
      (inferInstance : MeasurableSpace (J → X)) := by
    let D : J → Set (Set X) := fun _ => {s | MeasurableSet s}
    have hDC : Set.pi Set.univ '' Set.pi Set.univ D = C i := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t, ?_, rfl⟩
        simpa only [D, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq] using ht
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t, ?_, rfl⟩
        simpa only [D, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq] using ht
    rw [← hDC]
    exact generateFrom_eq_pi (fun _ => MeasurableSpace.generateFrom_measurableSet)
      (fun j => (μ i j).toFiniteSpanningSetsIn.isCountablySpanning)
  have hC_pi (i : I) : IsPiSystem (C i) := by
    let D : J → Set (Set X) := fun _ => {s | MeasurableSet s}
    have hDC : Set.pi Set.univ '' Set.pi Set.univ D = C i := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, by simpa [D] using ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, by simpa [D] using ht, rfl⟩
    rw [← hDC]
    exact IsPiSystem.pi fun _ => MeasurableSpace.isPiSystem_measurableSet
  have hC_span (i : I) :
      (Measure.pi fun j : J => μ i j).FiniteSpanningSetsIn (C i) := by
    let D : J → Set (Set X) := fun _ => {s | MeasurableSet s}
    have h := Measure.FiniteSpanningSetsIn.pi
      (fun j : J => (μ i j).toFiniteSpanningSetsIn)
    apply h.mono
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    simpa only [D, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq] using ht
  refine ⟨(MeasurableEquiv.curry I J X).measurable, ?_⟩
  symm
  apply Measure.pi_eq_generateFrom hC_generate hC_pi hC_span
  intro s hs
  choose t ht_meas ht_eq using fun i => hs i
  have hs_eq : s = fun i => Set.pi Set.univ (t i) := funext ht_eq
  subst s
  rw [MeasurableEquiv.map_apply]
  have hset : (MeasurableEquiv.curry I J X) ⁻¹'
      (Set.pi Set.univ fun i => Set.pi Set.univ (t i)) =
      Set.pi Set.univ fun ij : I × J => t ij.1 ij.2 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      MeasurableEquiv.coe_curry, Function.curry, Prod.forall]
  rw [hset, Measure.pi_pi]
  change (∏ ij : I × J, μ ij.1 ij.2 (t ij.1 ij.2)) =
    ∏ i : I, (Measure.pi fun j : J => μ i j) (Set.univ.pi (t i))
  simp_rw [Measure.pi_pi]
  exact Fintype.prod_prod_type (fun ij : I × J => μ ij.1 ij.2 (t ij.1 ij.2))

/-- All particle positions, with the flat configuration coordinates regrouped
by particle. -/
def particlePositions {N : ℕ} (x : Configuration N) : Fin N → Position :=
  fun i => particlePosition x i

/-- Regrouping flat configuration coordinates by particle is a measurable
equivalence. -/
def particlePositionsEquiv (N : ℕ) : Configuration N ≃ᵐ (Fin N → Position) where
  toFun := particlePositions
  invFun := fun y => WithLp.toLp 2 (fun ia => y ia.1 ia.2)
  left_inv := by
    intro x
    apply PiLp.ext
    intro ia
    rfl
  right_inv := by
    intro y
    funext i
    apply PiLp.ext
    intro a
    rfl
  measurable_toFun := measurable_pi_iff.mpr fun i => measurable_particlePosition i
  measurable_invFun := (PiLp.continuous_toLp 2
    (fun _ : Fin N × Fin 3 => ℝ)).measurable.comp
      (measurable_pi_iff.mpr fun ia =>
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ia.2).measurable.comp
          (measurable_pi_apply ia.1))

/-- Lebesgue measure on configuration space becomes the finite product of
physical one-particle Lebesgue measures. -/
theorem measurePreserving_particlePositions (N : ℕ) :
    MeasurePreserving (particlePositionsEquiv N) volume
      (Measure.pi fun _ : Fin N => (volume : Measure Position)) := by
  let A : Configuration N → Fin N × Fin 3 → ℝ := WithLp.ofLp
  let B : (Fin N × Fin 3 → ℝ) → Fin N → Fin 3 → ℝ := Function.curry
  let C : (Fin N → Fin 3 → ℝ) → Fin N → Position :=
    fun x i => WithLp.toLp 2 (x i)
  have hA : MeasurePreserving A volume
      (Measure.pi fun _ : Fin N × Fin 3 => (volume : Measure ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin N × Fin 3)
  have hB : MeasurePreserving B
      (Measure.pi fun _ : Fin N × Fin 3 => (volume : Measure ℝ))
      (Measure.pi fun _ : Fin N =>
        Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) := by
    simpa only [B, MeasurableEquiv.coe_curry] using
      (measurePreserving_curry_pi
        (fun _ : Fin N => fun _ : Fin 3 => (volume : Measure ℝ)))
  have hC : MeasurePreserving C
      (Measure.pi fun _ : Fin N =>
        Measure.pi fun _ : Fin 3 => (volume : Measure ℝ))
      (Measure.pi fun _ : Fin N => (volume : Measure Position)) := by
    exact MeasureTheory.measurePreserving_pi _ _ fun _ =>
      PiLp.volume_preserving_toLp (Fin 3)
  have h := hC.comp (hB.comp hA)
  have hf : C ∘ B ∘ A = particlePositions := by
    rfl
  rw [hf] at h
  change MeasurePreserving particlePositions volume
    (Measure.pi fun _ : Fin N => (volume : Measure Position))
  exact h

/-- The preimage of the product of the assigned open cubes is the open
assignment cell. -/
theorem particlePositionsEquiv_preimage_pi_cubeInterior {N : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex) :
    particlePositionsEquiv N ⁻¹'
        (Set.univ.pi fun i => cubeInterior (latticeCorner ℓ.val (b i)) ℓ) =
      openAssignmentCell ℓ.val b := by
  ext x
  have heval : particlePositionsEquiv N x = particlePositions x := rfl
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
    heval, particlePositions, cubeInterior, Set.mem_ofPred_eq,
    openAssignmentCell, latticeCorner, PiLp.toLp_apply]
  constructor
  · intro h i a
    have ha := h i a
    constructor
    · exact ha.1
    · simpa only [mul_add, mul_one] using ha.2
  · intro h i a
    have ha := h i a
    constructor
    · exact ha.1
    · simpa only [mul_add, mul_one] using ha.2

/-- Restricted configuration volume on an open assignment cell is exactly the
finite product of the restricted physical cube volumes. -/
theorem measurePreserving_particlePositions_restrict_openAssignmentCell {N : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex) :
    MeasurePreserving (particlePositionsEquiv N)
      (volume.restrict (openAssignmentCell ℓ.val b))
      (Measure.pi fun i : Fin N =>
        volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)) := by
  let S : Set (Fin N → Position) :=
    Set.univ.pi fun i => cubeInterior (latticeCorner ℓ.val (b i)) ℓ
  have hS : MeasurableSet S :=
    MeasurableSet.univ_pi fun i => measurableSet_cubeInterior (latticeCorner ℓ.val (b i)) ℓ
  have h := (measurePreserving_particlePositions N).restrict_preimage hS
  rw [particlePositionsEquiv_preimage_pi_cubeInterior ℓ b] at h
  rw [Measure.restrict_pi_pi] at h
  exact h

end

end LiebThirring.TFProduct

end
