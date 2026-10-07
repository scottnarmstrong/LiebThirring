/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.FilledEnumeration
public import LiebThirring.TFUpper.DirichletKineticState
public import LiebThirring.TFUpper.CubeSupportGeometry
import LiebThirring.TFUpper.DirichletInner
import LiebThirring.TFUpper.DirichletSupport

/-! # The actual occupied family of Dirichlet cube orbitals

The family consists of the literal zero-extended sine products, with one spin
label for each occupied lattice mode. It is enumerated at exactly the floored
particle count. Its orthonormality uses only interval orthogonality and disjoint
cube supports. Source: Lieb–Simon (1977) III.11/III.13--III.14, the cube spectral theory/Slater upper bound.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal InnerProductSpace
namespace LiebThirring.TFUpper

/-- The explicit orbital attached to an occupied cube/mode pair. -/
noncomputable def occupiedCubeOrbital {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) (i : OccupiedModeIndex q hq g α) : State 1 q :=
  dirichletCubeOrbital g.side (latticeCorner g.side.val (g.label i.1))
    (occupiedPositiveMode q hq g α i)

/-- The normalized sine-product orbitals at the literal floored particle count. -/
noncomputable def cubeTrialOrbitals {B : ℕ} (q : {q : ℕ // 1 ≤ q})
    (g : CubeMesh B) (α : ℝ≥0) :
    Fin (occupationCount α g.mass) → State 1 q.val :=
  occupiedCubeOrbital q.val q.property g α ∘ occupiedModeEquiv q.val q.property g α

theorem orthonormal_occupiedCubeOrbital {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :
    Orthonormal ℂ (occupiedCubeOrbital q hq g α) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℂ
    (spatialSpinToState q (dirichletCubeSpatialL2 g.side
      (latticeCorner g.side.val (g.label i.1)) (occupiedPositiveMode q hq g α i)))
    (spatialSpinToState q (dirichletCubeSpatialL2 g.side
      (latticeCorner g.side.val (g.label j.1)) (occupiedPositiveMode q hq g α j))) = _
  rw [(spatialSpinToState q).inner_map_map]
  by_cases hb : i.1 = j.1
  · rw [hb, inner_dirichletCubeSpatialL2]
    have heq : occupiedPositiveMode q hq g α i = occupiedPositiveMode q hq g α j ↔
        i = j := by
      constructor
      · intro hm
        exact occupiedModePair_injective q hq g α (Prod.ext hb hm)
      · intro h
        exact congrArg (occupiedPositiveMode q hq g α) h
    simp only [heq]
  · have hij : i ≠ j := fun h => hb (congrArg Sigma.fst h)
    rw [ite_eq_right hij]
    exact inner_dirichletCubeSpatialL2_eq_zero_of_disjoint g.side _ _ _ _
      (g.disjoint_cubeInteriors hb)

theorem orthonormal_cubeTrialOrbitals {B : ℕ} (q : {q : ℕ // 1 ≤ q})
    (g : CubeMesh B) (α : ℝ≥0) : Orthonormal ℂ (cubeTrialOrbitals q g α) :=
  (orthonormal_occupiedCubeOrbital q.val q.property g α).comp
    (occupiedModeEquiv q.val q.property g α)
    (occupiedModeEquiv q.val q.property g α).injective

/-- All occupied orbitals share a single bounded support, including the empty mesh. -/
theorem cubeTrialOrbitals_compact_support {B : ℕ} (q : {q : ℕ // 1 ≤ q})
    (g : CubeMesh B) (α : ℝ≥0) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ i, ∀ᵐ x : Position,
      S < ‖x‖ → orbitalValue (cubeTrialOrbitals q g α i) x = 0 := by
  obtain ⟨S, hS, hbound⟩ := g.exists_support_radius
  refine ⟨S, hS, ?_⟩
  intro i
  let j := occupiedModeEquiv q.val q.property g α i
  have hrep : ∀ᵐ x : Position, ∀ t : Fin q.val,
      orbitalValue (cubeTrialOrbitals q g α i) x t =
        (TFCubes.cubeInterior (latticeCorner g.side.val (g.label j.1)) g.side).indicator
          (TFCubes.dirichletCubeModeValue g.side
            (latticeCorner g.side.val (g.label j.1))
              (occupiedPositiveMode q.val q.property g α j)) x t := by
    apply ae_all_iff.mpr
    intro t
    exact orbitalValue_dirichletCubeOrbital_ae g.side _ _ t
  filter_upwards [hrep] with x hx hnorm
  have hnot : x ∉ TFCubes.cubeInterior
      (latticeCorner g.side.val (g.label j.1)) g.side := by
    intro hmem
    exact (not_le_of_gt hnorm) (hbound j.1 x hmem)
  funext t
  rw [hx t, Set.indicator_of_notMem hnot]
  rfl

end LiebThirring.TFUpper
end
