/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.MeshDensity
import LiebThirring.TFLattice.CellBoundary

/-! # Consumption of the proved lattice-density limits

The canonical filled density inherits lattice density estimates's floor/multicube convergence in the
exact Ico mesh convention. Source: Lieb–Simon (1977) III.14 (68)–(71), pp.69–71.
-/

public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace LiebThirring.TFFilled
open TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨one_le_five_thirds⟩

/-- The proved scalar filled-density convergence limit on the actual normalized mesh representatives. -/
theorem tendsto_lpNorm_normalizedMeshDensity_sub_of_lattice
    {B : ℕ} (q : ℕ) (hq : 0 < q) (g : CubeMesh B)
    (ρ : TFDensity) (hstep : g.represents ρ)
    {ι : Type*} {l : Filter ι} {a : ι → ℝ≥0}
    (ha : Tendsto (fun j => (a j : ℝ)) l atTop)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Tendsto (fun j => lpNorm (fun x =>
      (normalizedMeshDensity q hq g (a j)).val x - ρ.val x) p volume) l (𝓝 0) := by
  have ht := (TFLattice.tendsto_lpNorm_floor_lattice_density hq g.side g.label ha
    (fun b => (g.mass b : ℝ)) (fun b => (g.mass b).coe_nonneg)
    (fun j => meshOccupations q hq g (a j))
    (fun j => isFilled_meshOccupations q hq g (a j))
    (fun j => card_meshOccupations q hq g (a j)) hp1 hp2).2
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [normalizedMeshDensity_ae q hq g (a j), hstep] with x hd hρ
  rw [hd, hρ]
  rfl

/-- Genuine carrier convergence supplied by the proved scalar filled-density convergence theorem. -/
theorem tendsto_normalizedMeshDensity_of_lattice
    {B : ℕ} (q : ℕ) (hq : 0 < q) (g : CubeMesh B)
    (ρ : TFDensity) (hstep : g.represents ρ)
    {ι : Type*} {l : Filter ι} {a : ι → ℝ≥0}
    (ha : Tendsto (fun j => (a j : ℝ)) l atTop) :
    Tendsto (fun j => (normalizedMeshDensity q hq g (a j)).val) l (𝓝 ρ.val) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := tendsto_lpNorm_normalizedMeshDensity_sub_of_lattice q hq g ρ hstep ha
    one_le_five_thirds five_thirds_le_two
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  change lpNorm (fun x => (normalizedMeshDensity q hq g (a j)).val x - ρ.val x)
    ((5 : ℝ≥0∞) / 3) volume = ‖(normalizedMeshDensity q hq g (a j)).val - ρ.val‖
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm

/-- The exact L¹ integral limit supplied by the proved scalar filled-density convergence theorem. -/
theorem tendsto_integral_abs_normalizedMeshDensity_sub_of_lattice
    {B : ℕ} (q : ℕ) (hq : 0 < q) (g : CubeMesh B)
    (ρ : TFDensity) (hstep : g.represents ρ)
    {ι : Type*} {l : Filter ι} {a : ι → ℝ≥0}
    (ha : Tendsto (fun j => (a j : ℝ)) l atTop) :
    Tendsto (fun j => ∫ x : Position,
      |(normalizedMeshDensity q hq g (a j)).val x - ρ.val x|) l (𝓝 (0 : ℝ)) := by
  have ht := tendsto_lpNorm_normalizedMeshDensity_sub_of_lattice q hq g ρ hstep ha
    (le_refl 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply ht.congr'
  exact Eventually.of_forall fun j => lpNorm_one_eq_integral_abs
    ((Lp.aestronglyMeasurable (normalizedMeshDensity q hq g (a j)).val).sub
      (Lp.aestronglyMeasurable ρ.val))

end LiebThirring.TFFilled
end
