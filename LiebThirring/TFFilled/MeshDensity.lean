/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.MulticubeDensity
public import LiebThirring.TFUpper.CubeStep
public import LiebThirring.TFUpper.Occupation
public import LiebThirring.TFFunctional.TrialDensities
public import LiebThirring.TFFunctional.Operations

/-! # Actual TF densities from floored Dirichlet occupations

Use exactly TFUpper's occupation selector and cube mesh. The divided literal
finite sum is packaged on the nonnegative L¹ ∩ L⁵ᐟ³ carrier, including
zero charge and zero-mass cubes. Proof: filled-density convergence–Slater upper bound, Lieb–Simon (1977) III.14 pp.69–71.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFFilled
open TFUpper TFLattice

theorem one_le_five_thirds : (1 : ℝ≥0∞) ≤ 5 / 3 := by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]

theorem five_thirds_le_two : (5 : ℝ≥0∞) / 3 ≤ 2 := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by simp)).mp
  norm_num [ENNReal.toReal_div]

/-- The half-open translated cube corners of the actual upper-bound mesh. -/
noncomputable def meshCorners {B : ℕ} (g : CubeMesh B) : Fin B → Position :=
  fun b => latticeCorner g.side.val (g.label b)

/-- The precise filled-mode selections used by the upper-bound occupation count. -/
noncomputable def meshOccupations {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) : Fin B → Finset (ModeIndex q) :=
  fun b => filledDirichletModes q hq (cubeOccupation a (g.mass b))

theorem card_meshOccupations {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) (b : Fin B) :
    (meshOccupations q hq g a b).card = ⌊(a : ℝ) * (g.mass b : ℝ)⌋₊ :=
  card_filledDirichletModes q hq _

theorem isFilled_meshOccupations {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) (b : Fin B) :
    IsFilled IsDirichletIndex (meshOccupations q hq g a b) :=
  isFilled_filledDirichletModes q hq _

/-- The literal physical sum, counting each occupied spin-labelled mode once. -/
noncomputable def meshFilledDensity {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) : Position → ℝ :=
  multicubeDensity g.side (meshCorners g) (meshOccupations q hq g a)

/-- The literal divided density; at charge zero it is zero everywhere. -/
noncomputable def normalizedMeshDensityFn {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) (x : Position) : ℝ :=
  meshFilledDensity q hq g a x / (a : ℝ)

theorem normalizedMeshDensityFn_nonneg {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) (x : Position) :
    0 ≤ normalizedMeshDensityFn q hq g a x :=
  div_nonneg (multicubeDensity_nonneg _ _ _ _) a.property

theorem memLp_normalizedMeshDensityFn {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) {p : ℝ≥0∞} (hp : p ≤ 2) :
    MemLp (normalizedMeshDensityFn q hq g a) p volume := by
  have h := (memLp_multicubeDensity g.side (meshCorners g)
    (meshOccupations q hq g a) hp).const_smul (a : ℝ)⁻¹
  have heq : normalizedMeshDensityFn q hq g a =
      (a : ℝ)⁻¹ • multicubeDensity g.side (meshCorners g) (meshOccupations q hq g a) := by
    funext x
    change _ / (a : ℝ) = (a : ℝ)⁻¹ * _
    rw [div_eq_mul_inv, mul_comm]
    rfl
  rw [heq]
  exact h

theorem integrable_normalizedMeshDensityFn {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) : Integrable (normalizedMeshDensityFn q hq g a) :=
  memLp_one_iff_integrable.mp (memLp_normalizedMeshDensityFn q hq g a (by norm_num))

/-- The divided lowest-mode density as a genuine TF density. -/
noncomputable def normalizedMeshDensity {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) : TFDensity :=
  TFFunctional.tfDensityOfFunction (normalizedMeshDensityFn q hq g a)
    (memLp_normalizedMeshDensityFn q hq g a five_thirds_le_two)
    (Filter.Eventually.of_forall (normalizedMeshDensityFn_nonneg q hq g a))
    (integrable_normalizedMeshDensityFn q hq g a)

theorem normalizedMeshDensity_ae {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) :
    (normalizedMeshDensity q hq g a).val =ᵐ[volume] normalizedMeshDensityFn q hq g a :=
  TFFunctional.tfDensityOfFunction_coeFn _ _ _ _

/-- All selected mode sets are genuinely empty when the charge is zero. -/
theorem meshOccupations_zero {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (b : Fin B) : meshOccupations q hq g 0 b = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_meshOccupations, NNReal.coe_zero, zero_mul, Nat.floor_zero]

theorem meshFilledDensity_zero {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) : meshFilledDensity q hq g 0 = 0 := by
  funext x
  simp only [meshFilledDensity, multicubeDensity, meshOccupations_zero,
    physicalFilledDensity, filledDensity, Finset.sum_empty, indicator_zero,
    Finset.sum_const_zero, Pi.zero_apply]

/-- Reconstruction holds for every charge, including zero, as required by TFUpper. -/
theorem tfDensitySMul_normalizedMeshDensity_ae {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (a : ℝ≥0) :
    (TFFunctional.tfDensitySMul a (normalizedMeshDensity q hq g a)).val =ᵐ[volume]
      meshFilledDensity q hq g a := by
  filter_upwards [TFFunctional.tfDensitySMul_coeFn a (normalizedMeshDensity q hq g a),
    normalizedMeshDensity_ae q hq g a] with x hs hd
  rw [hs, hd, normalizedMeshDensityFn]
  by_cases ha : a = 0
  · subst a
    rw [meshFilledDensity_zero]
    simp only [NNReal.coe_zero, Pi.zero_apply, zero_div, mul_zero]
  · exact mul_div_cancel₀ _ (by exact_mod_cast ha)

end LiebThirring.TFFilled
end
