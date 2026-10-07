/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.ModeDensities
public import LiebThirring.TFLattice.CoordinateCollisions
public import LiebThirring.TFLattice.OccupationRadius
import Mathlib.Tactic

/-!
# Quantitative variance of filled Dirichlet densities

The centered square integral counts only pairs sharing a spatial coordinate.
The proof uses exact sine-product integrals, not pointwise convergence.
Source: Lieb–Simon (1977) III.14, (68)–(71), pp. 69–71.
-/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFLattice

instance (ℓ : {ℓ : ℝ // 0 < ℓ}) : IsFiniteMeasure (cubeCoordinateMeasure ℓ) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Fin 3 =>
    volume.restrict (Set.Ioc 0 ℓ.val)))

theorem cubeCoordinateMeasure_real_univ (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    (cubeCoordinateMeasure ℓ).real Set.univ = ℓ.val ^ 3 := by
  unfold Measure.real cubeCoordinateMeasure
  rw [Measure.pi_univ]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow ℓ.property.le, ENNReal.toReal_ofReal (pow_nonneg ℓ.property.le _)]

theorem integrable_filledDensity {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) : Integrable (filledDensity ℓ s) (cubeCoordinateMeasure ℓ) :=
  integrable_finsetSum s fun p _ => integrable_spatialModeDensity ℓ p.1

theorem filledDensity_sq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) (x : Fin 3 → ℝ) :
    filledDensity ℓ s x ^ 2 = ∑ k ∈ s, ∑ p ∈ s,
      spatialModeDensity ℓ k.1 x * spatialModeDensity ℓ p.1 x := by
  simp only [filledDensity, pow_two, Finset.sum_mul_sum]

theorem integrable_filledDensity_sq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) :
    Integrable (fun x => filledDensity ℓ s x ^ 2) (cubeCoordinateMeasure ℓ) := by
  simp_rw [filledDensity_sq]
  exact integrable_finsetSum s fun k _ => integrable_finsetSum s fun p _ =>
    integrable_spatialModeDensity_mul ℓ k.1 p.1

theorem integral_filledDensity_sq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) :
    (∫ x, filledDensity ℓ s x ^ 2 ∂cubeCoordinateMeasure ℓ) =
      ∑ k ∈ s, ∑ p ∈ s, ∫ x,
        spatialModeDensity ℓ k.1 x * spatialModeDensity ℓ p.1 x ∂cubeCoordinateMeasure ℓ := by
  simp_rw [filledDensity_sq]
  rw [integral_finsetSum s (fun k _ => integrable_finsetSum s fun p _ =>
    integrable_spatialModeDensity_mul ℓ k.1 p.1)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_finsetSum s fun p _ => integrable_spatialModeDensity_mul ℓ k.1 p.1

/-- Exact cancellation of the constant-density baseline. -/
theorem integral_filledDensity_sub_sq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) (hs : ∀ p ∈ s, IsDirichletIndex p) :
    (∫ x, (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 ∂cubeCoordinateMeasure ℓ) =
      ∑ k ∈ s, ∑ p ∈ s,
        ((∫ x, spatialModeDensity ℓ k.1 x * spatialModeDensity ℓ p.1 x
          ∂cubeCoordinateMeasure ℓ) - 1 / ℓ.val ^ 3) := by
  have heq (x : Fin 3 → ℝ) : (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 =
      filledDensity ℓ s x ^ 2 - (2 * (s.card / ℓ.val ^ 3)) * filledDensity ℓ s x +
        (s.card / ℓ.val ^ 3) ^ 2 := by ring
  simp_rw [heq]
  rw [integral_add (f := fun x => filledDensity ℓ s x ^ 2 -
      (2 * (s.card / ℓ.val ^ 3)) * filledDensity ℓ s x)
      (g := fun _ => (s.card / ℓ.val ^ 3) ^ 2)
      ((integrable_filledDensity_sq ℓ s).sub
        ((integrable_filledDensity ℓ s).const_mul _)) (integrable_const _),
    integral_sub (f := fun x => filledDensity ℓ s x ^ 2)
      (g := fun x => (2 * (s.card / ℓ.val ^ 3)) * filledDensity ℓ s x)
      (integrable_filledDensity_sq ℓ s) ((integrable_filledDensity ℓ s).const_mul _),
    integral_const_mul, integral_const, integral_filledDensity ℓ s hs,
    cubeCoordinateMeasure_real_univ, smul_eq_mul, integral_filledDensity_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hℓ : ℓ.val ≠ 0 := ℓ.property.ne'
  field_simp
  ring

theorem integral_spatialModeDensity_mul_le (ℓ : {ℓ : ℝ // 0 < ℓ})
    {k p : Fin 3 → ℕ} (hk : ∀ i, 0 < k i) (hp : ∀ i, 0 < p i) :
    (∫ x, spatialModeDensity ℓ k x * spatialModeDensity ℓ p x ∂cubeCoordinateMeasure ℓ) ≤
      8 / ℓ.val ^ 3 := by
  have hℓ : 0 < ℓ.val := ℓ.property
  rw [integral_spatialModeDensity_mul ℓ hk hp]
  calc
    _ ≤ ∏ _ : Fin 3, 2 / ℓ.val := by
      apply Finset.prod_le_prod₀
      · intro i _
        split_ifs <;> positivity
      · intro i _
        split_ifs <;> apply (div_le_div_iff₀ (by positivity) ℓ.property).mpr <;> nlinarith
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]; norm_num

theorem integral_spatialModeDensity_mul_sub_le (ℓ : {ℓ : ℝ // 0 < ℓ})
    {k p : Fin 3 → ℕ} (hk : ∀ i, 0 < k i) (hp : ∀ i, 0 < p i) :
    (∫ x, spatialModeDensity ℓ k x * spatialModeDensity ℓ p x ∂cubeCoordinateMeasure ℓ) -
      1 / ℓ.val ^ 3 ≤ if ∃ i, p i = k i then 8 / ℓ.val ^ 3 else 0 := by
  classical
  have hℓ : 0 < ℓ.val := ℓ.property
  split_ifs with h
  · have hi := integral_spatialModeDensity_mul_le ℓ hk hp
    have hz : 0 ≤ 1 / ℓ.val ^ 3 := by positivity
    linarith
  · have hne : ∀ i, k i ≠ p i := by
      intro i heq
      exact h ⟨i, heq.symm⟩
    rw [integral_spatialModeDensity_mul ℓ hk hp]
    simp only [ite_eq_right (hne _), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      div_pow, one_pow, sub_self, le_refl]

/-- Variance bound for every positive-coordinate occupation in a box,
without a spectral filling hypothesis. -/
theorem integral_filledDensity_sub_sq_le_box {q a m : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : ∀ p ∈ s, IsDirichletIndex p) (hbox : s ⊆ modeBox q a m) :
    (∫ x, (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 ∂cubeCoordinateMeasure ℓ) ≤
      24 * q * s.card * m ^ 2 / ℓ.val ^ 3 := by
  classical
  have hℓ : 0 < ℓ.val := ℓ.property
  rw [integral_filledDensity_sub_sq ℓ s hs]
  calc
    _ ≤ ∑ k ∈ s, ∑ p ∈ s,
        if ∃ i, p.1 i = k.1 i then 8 / ℓ.val ^ 3 else 0 := by
      exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun p hp =>
        integral_spatialModeDensity_mul_sub_le ℓ (hs k hk) (hs p hp)
    _ = (8 / ℓ.val ^ 3) *
        ((∑ k ∈ s, (s.filter fun p => ∃ i, p.1 i = k.1 i).card : ℕ) : ℝ) := by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (8 / ℓ.val ^ 3) * (s.card * (3 * q * m ^ 2) : ℕ) := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast sum_card_shared_coordinate_partners_le hbox
      · positivity
    _ = _ := by push_cast; ring

end LiebThirring.TFLattice

end
