/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.MeshDensity
public import LiebThirring.TFUpper.FilledEnumeration
public import LiebThirring.TFUpper.DirichletKineticState
public import LiebThirring.TFQuantum.SlaterMarginals

/-! # Density of the filled-cube orbital family

The spin-summed density of the explicitly enumerated Dirichlet orbitals is the
literal filled-mode density used in the multicube approximation. This is the
density representation in Lieb–Simon (1977) III.14, equations (68)--(71), pp. 69--71
(the filled-density convergence).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal

namespace LiebThirring.TFFilled

open TFCubes TFLattice TFUpper

/-- The orbital attached to one occupied cube/mode pair. -/
noncomputable def occupiedFilledCubeOrbital {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) (i : OccupiedModeIndex q hq g a) : State 1 q :=
  dirichletCubeOrbital g.side (meshCorners g i.1)
    (occupiedPositiveMode q hq g a i)

/-- The literal filled-cube orbitals, enumerated by their exact floor count. -/
noncomputable def filledCubeOrbitals {B : ℕ} (q : {q : ℕ // 1 ≤ q})
    (g : CubeMesh B) (a : ℝ≥0) :
    Fin (occupationCount a g.mass) → State 1 q.val :=
  occupiedFilledCubeOrbital q.val q.property g a ∘
    occupiedModeEquiv q.val q.property g a

/- This family is definitionally the same family as `TFUpper.cubeTrialOrbitals`
once that module's orthogonality layer is available. -/

private theorem cubeInterior_ae_eq_physicalCube
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :
    TFCubes.cubeInterior b ℓ =ᵐ[volume] TFLattice.physicalCube ℓ b := by
  have he : (Set.univ.pi fun _ : Fin 3 => Ioo (0 : ℝ) ℓ.val) =ᵐ[volume]
      Set.univ.pi fun _ : Fin 3 => Ioc (0 : ℝ) ℓ.val :=
    Measure.ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc
  have hp := (TFCubes.measurePreserving_cubeCoordinates b).quasiMeasurePreserving.preimage_ae_eq he
  rw [TFCubes.cubeCoordinates_preimage_intervalCube] at hp
  convert hp using 1
  ext x
  simp only [TFLattice.physicalCube, TFLattice.cubeCoordinateSet, mem_preimage,
    Set.mem_pi, mem_univ, forall_const, mem_Ioc]
  rfl

private theorem sum_norm_sq_dirichletCubeModeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : DirichletCubeModeIndex q) (x : Position) :
    (∑ t : Fin q, ‖dirichletCubeModeValue ℓ b p x t‖ ^ 2) =
      spatialModeDensity ℓ (fun i => (p.1 i : ℕ))
        (TFLattice.cubeCoordinates b x) := by
  rw [← PiLp.norm_sq_eq_of_L2, dirichletCubeModeValue, PiLp.norm_single,
    dirichletCubeSpatialMode, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, ← Finset.prod_pow, sq_abs,
    spatialModeDensity]
  apply Finset.prod_congr rfl
  intro i _
  rw [dirichletFactorDensity_eq_sq]
  rfl

theorem slaterOrbitalDensity_filledCubeOrbitals_ae {B : ℕ}
    (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (a : ℝ≥0) :
    slaterOrbitalDensity (filledCubeOrbitals q g a) =ᵐ[volume]
      meshFilledDensity q.val q.property g a := by
  have horb : ∀ᵐ x : Position, ∀ i : Fin (occupationCount a g.mass), ∀ t : Fin q.val,
      orbitalValue (filledCubeOrbitals q g a i) x t =
        (cubeInterior
          (latticeCorner g.side.val
            (g.label (occupiedModeEquiv q.val q.property g a i).1)) g.side).indicator
          (dirichletCubeModeValue g.side
            (latticeCorner g.side.val
              (g.label (occupiedModeEquiv q.val q.property g a i).1))
            (occupiedPositiveMode q.val q.property g a
              (occupiedModeEquiv q.val q.property g a i))) x t := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro t
    exact orbitalValue_dirichletCubeOrbital_ae g.side _ _ t
  have hcubes : ∀ᵐ x : Position, ∀ b : Fin B,
      (x ∈ cubeInterior (meshCorners g b) g.side ↔
        x ∈ physicalCube g.side (meshCorners g b)) :=
    ae_all_iff.mpr fun b =>
      (cubeInterior_ae_eq_physicalCube g.side (meshCorners g b)).mono
        fun _ hx => iff_of_eq hx
  filter_upwards [horb, hcubes] with x hx hc
  rw [slaterOrbitalDensity, Finset.sum_comm]
  simp_rw [hx]
  rw [(occupiedModeEquiv q.val q.property g a).sum_comp
      (fun i : OccupiedModeIndex q.val q.property g a =>
        ∑ t : Fin q.val, ‖(cubeInterior
          (latticeCorner g.side.val (g.label i.1)) g.side).indicator
          (dirichletCubeModeValue g.side
            (latticeCorner g.side.val (g.label i.1))
            (occupiedPositiveMode q.val q.property g a i)) x t‖ ^ 2),
    Fintype.sum_sigma]
  change (∑ b : Fin B,
      ∑ i : ↥(filledDirichletModes q.val q.property (cubeOccupation a (g.mass b))),
      ∑ t : Fin q.val, ‖(cubeInterior (meshCorners g b) g.side).indicator
        (dirichletCubeModeValue g.side (meshCorners g b)
          (occupiedPositiveMode q.val q.property g a ⟨b, i⟩)) x t‖ ^ 2) = _
  rw [meshFilledDensity, multicubeDensity]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hxi : x ∈ cubeInterior (meshCorners g b) g.side
  · rw [physicalFilledDensity, indicator_of_mem ((hc b).mp hxi)]
    simp only [indicator_of_mem hxi, filledDensity]
    rw [meshOccupations]
    calc
      _ = ∑ i : ↥(filledDirichletModes q.val q.property
          (cubeOccupation a (g.mass b))),
          spatialModeDensity g.side i.val.1
            (TFLattice.cubeCoordinates (meshCorners g b) x) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sum_norm_sq_dirichletCubeModeValue]
        rfl
      _ = _ := Finset.sum_coe_sort
        (filledDirichletModes q.val q.property (cubeOccupation a (g.mass b)))
        (fun p => spatialModeDensity g.side p.1
          (TFLattice.cubeCoordinates (meshCorners g b) x))
  · rw [physicalFilledDensity, indicator_of_notMem (fun h => hxi ((hc b).mpr h))]
    simp [indicator_of_notMem hxi]

end LiebThirring.TFFilled

end
