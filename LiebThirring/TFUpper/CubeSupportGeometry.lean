/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.CubeStep
public import LiebThirring.TFCubes.CubeModes

/-! # Disjointness and bounded support of the trial mesh

Open sine-product cubes lie in the literal half-open lattice cells of the TF
mesh. The finite collection lies in one explicitly bounded ball. These facts
give cross-cube orthogonality and the support needed for exact-particle repair.
direct proof finite-mesh geometry.
-/

public section
open Set
namespace LiebThirring.TFUpper

theorem cubeInterior_latticeCorner_subset_cell
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (z : LatticeIndex) :
    TFCubes.cubeInterior (latticeCorner ℓ.val z) ℓ ⊆ latticeCell ℓ.val z := by
  intro x hx a
  have ha := hx a
  change ℓ.val * (z a : ℝ) ≤ x a ∧ x a < ℓ.val * ((z a : ℝ) + 1)
  change ℓ.val * (z a : ℝ) < x a ∧ x a < ℓ.val * (z a : ℝ) + ℓ.val at ha
  exact ⟨ha.1.le, by linarith only [ha.2]⟩

theorem CubeMesh.disjoint_cubeInteriors {B : ℕ} (g : CubeMesh B)
    {b c : Fin B} (hbc : b ≠ c) :
    Disjoint (TFCubes.cubeInterior (latticeCorner g.side.val (g.label b)) g.side)
      (TFCubes.cubeInterior (latticeCorner g.side.val (g.label c)) g.side) :=
  (latticeCell_disjoint g.side.property (fun h => hbc (g.distinct h))).mono
    (cubeInterior_latticeCorner_subset_cell g.side (g.label b))
    (cubeInterior_latticeCorner_subset_cell g.side (g.label c))

/-- A single positive radius contains every cube in the finite mesh. -/
theorem CubeMesh.exists_support_radius {B : ℕ} (g : CubeMesh B) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ b : Fin B, ∀ x : Position,
      x ∈ TFCubes.cubeInterior (latticeCorner g.side.val (g.label b)) g.side →
        ‖x‖ ≤ S := by
  let C : ℝ := ∑ b, ‖latticeCorner g.side.val (g.label b)‖
  let S : ℝ := C + Real.sqrt 3 * g.side.val + 1
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hd : 0 ≤ Real.sqrt 3 * g.side.val :=
    mul_nonneg (Real.sqrt_nonneg _) g.side.property.le
  refine ⟨S, by dsimp only [S]; linarith only [hC, hd], ?_⟩
  intro b x hx
  have hb : ‖latticeCorner g.side.val (g.label b)‖ ≤ C :=
    Finset.single_le_sum (f := fun b => ‖latticeCorner g.side.val (g.label b)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
  have hxclosed := latticeCell_subset_closedCell g.side.val (g.label b)
    (cubeInterior_latticeCorner_subset_cell g.side (g.label b) hx)
  have hdist := dist_le_lattice_diameter g.side.property.le hxclosed
    (latticeCorner_mem_closedCell g.side.property.le (g.label b))
  have hn : ‖x‖ ≤ dist x (latticeCorner g.side.val (g.label b)) +
      ‖latticeCorner g.side.val (g.label b)‖ := by
    rw [dist_eq_norm_sub]
    calc
      ‖x‖ = ‖(x - latticeCorner g.side.val (g.label b)) +
          latticeCorner g.side.val (g.label b)‖ :=
        congrArg norm (sub_add_cancel x _).symm
      _ ≤ _ := norm_add_le _ _
  dsimp only [S]
  linarith only [hn, hdist, hb]

end LiebThirring.TFUpper
end
