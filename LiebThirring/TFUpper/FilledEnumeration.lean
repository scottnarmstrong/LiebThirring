/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.Occupation
public import LiebThirring.TFUpper.CubeStep

/-! # Enumerating the occupied Dirichlet modes of a finite mesh

The finite index is the literal disjoint union of the selected lowest modes
in each cube. Reindexing by `Fin` preserves that occupation and its exact
eigenvalue sum. No basis completeness or spectral asymptotic is used.
Source: Lieb–Simon (1977) III.13--III.14, journal pp. 67--69.
-/

@[expose] public section
open scoped NNReal
namespace LiebThirring.TFUpper

/-- The literal occupied cube/mode pairs. -/
abbrev OccupiedModeIndex {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :=
  Σ b : Fin B, ↥(filledDirichletModes q hq (cubeOccupation α (g.mass b)))

theorem card_occupiedModeIndex {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :
    Fintype.card (OccupiedModeIndex q hq g α) = occupationCount α g.mass := by
  classical
  simp only [OccupiedModeIndex, Fintype.card_sigma, Fintype.card_coe,
    card_filledDirichletModes, occupationCount]

/-- A finite enumeration of exactly the modes actually selected in the mesh. -/
noncomputable def occupiedModeEquiv {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :
    Fin (occupationCount α g.mass) ≃ OccupiedModeIndex q hq g α :=
  (Fintype.equivFinOfCardEq (card_occupiedModeIndex q hq g α)).symm

/-- Every selected mode has strictly positive spatial frequencies. -/
theorem occupiedMode_isDirichlet {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) (i : OccupiedModeIndex q hq g α) :
    TFLattice.IsDirichletIndex i.2.val :=
  (isFilled_filledDirichletModes q hq (cubeOccupation α (g.mass i.1))).1
    i.2.val i.2.property

/-- Positive-coordinate version of an occupied mode, with the same spin. -/
def occupiedPositiveMode {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) (i : OccupiedModeIndex q hq g α) :
    (Fin 3 → ℕ+) × Fin q :=
  (fun a => ⟨i.2.val.1 a, occupiedMode_isDirichlet q hq g α i a⟩, i.2.val.2)

theorem occupiedPositiveMode_coe {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) (i : OccupiedModeIndex q hq g α) :
    ((fun a => ((occupiedPositiveMode q hq g α i).1 a : ℕ)),
      (occupiedPositiveMode q hq g α i).2) = i.2.val := rfl

theorem occupiedModePair_injective {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :
    Function.Injective (fun i : OccupiedModeIndex q hq g α =>
      (i.1, occupiedPositiveMode q hq g α i)) := by
  intro i j h
  have hb : i.1 = j.1 := congrArg Prod.fst h
  have hm : i.2.val = j.2.val := by
    rw [← occupiedPositiveMode_coe q hq g α i, ← occupiedPositiveMode_coe q hq g α j]
    exact congrArg (fun p : (Fin 3 → ℕ+) × Fin q =>
      ((fun a => (p.1 a : ℕ)), p.2)) (congrArg Prod.snd h)
  cases i with
  | mk b i =>
    cases j with
    | mk c j =>
      dsimp only at hb hm
      subst c
      exact congrArg (Sigma.mk b) (Subtype.ext hm)

/-- Enumeration preserves the actual occupied eigenvalue sum. -/
theorem sum_occupiedModeEquiv_eigenvalue {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) :
    (∑ i : Fin (occupationCount α g.mass),
      TFLattice.cubeEigenvalue g.side (occupiedModeEquiv q hq g α i).2.val) =
      occupiedCubeKinetic q hq g.side α g.mass := by
  classical
  rw [(occupiedModeEquiv q hq g α).sum_comp
    (fun i : OccupiedModeIndex q hq g α => TFLattice.cubeEigenvalue g.side i.2.val)]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_coe_sort, occupiedCubeKinetic]

end LiebThirring.TFUpper
end
