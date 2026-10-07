/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.Indices
public import LiebThirring.TFLattice.SineProducts
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Explicit spatial densities on a cube

The coordinate product measure is Lebesgue measure on `(0,ℓ]³`. Passing to
an open cube changes only a null boundary. Spin labels occur in the finite
occupation, and each occupied spatial-and-spin mode contributes one copy
of its spatial squared modulus. Source: Lieb–Simon (1977) III.14 (68)–(71),
pp. 69–71.
-/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFLattice

open TFCubes

noncomputable def cubeCoordinateMeasure (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Measure (Fin 3 → ℝ) := Measure.pi fun _ => volume.restrict (Set.Ioc 0 ℓ.val)

/-- Literal square of the normalized sine factor. Zero frequencies give zero;
all Dirichlet assertions below require positive coordinates. -/
noncomputable def dirichletFactorDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) : ℝ :=
  (2 / ℓ.val) * Real.sin (intervalFrequency ℓ n * x) ^ 2

noncomputable def spatialModeDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : Fin 3 → ℕ)
    (x : Fin 3 → ℝ) : ℝ := ∏ i, dirichletFactorDensity ℓ (k i) (x i)

noncomputable def filledDensity {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) (x : Fin 3 → ℝ) : ℝ :=
  ∑ p ∈ s, spatialModeDensity ℓ p.1 x

theorem dirichletFactorDensity_eq_sq (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) :
    dirichletFactorDensity ℓ n x = dirichletIntervalMode ℓ n x ^ 2 := by
  simp only [dirichletFactorDensity, dirichletIntervalMode, mul_pow,
    Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ℓ.property.le)]

theorem dirichletFactorDensity_nonneg (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) :
    0 ≤ dirichletFactorDensity ℓ n x := by
  exact mul_nonneg (div_nonneg (by norm_num) ℓ.property.le) (sq_nonneg _)

theorem spatialModeDensity_nonneg (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : Fin 3 → ℕ)
    (x : Fin 3 → ℝ) : 0 ≤ spatialModeDensity ℓ k x :=
  Finset.prod_nonneg fun _ _ => dirichletFactorDensity_nonneg _ _ _

theorem filledDensity_nonneg {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) (x : Fin 3 → ℝ) : 0 ≤ filledDensity ℓ s x :=
  Finset.sum_nonneg fun _ _ => spatialModeDensity_nonneg _ _ _

theorem integrable_dirichletFactorDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) :
    Integrable (dirichletFactorDensity ℓ n) (volume.restrict (Set.Ioc 0 ℓ.val)) := by
  have hc : Continuous (dirichletFactorDensity ℓ n) := by
    unfold dirichletFactorDensity
    fun_prop
  exact (hc.intervalIntegrable 0 ℓ.val).1

theorem integrable_spatialModeDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : Fin 3 → ℕ) :
    Integrable (spatialModeDensity ℓ k) (cubeCoordinateMeasure ℓ) :=
  Integrable.fintype_prod fun _ => integrable_dirichletFactorDensity _ _

theorem integral_dirichletFactorDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : 0 < n) :
    (∫ x, dirichletFactorDensity ℓ n x ∂(volume.restrict (Set.Ioc 0 ℓ.val))) = 1 := by
  have heq : dirichletFactorDensity ℓ n = fun x =>
      dirichletIntervalMode ℓ ⟨n, hn⟩ x ^ 2 := by
    ext x
    exact dirichletFactorDensity_eq_sq _ ⟨n, hn⟩ _
  rw [heq, ← intervalIntegral.integral_of_le ℓ.property.le]
  exact integral_dirichletIntervalMode_sq _ _

theorem integral_spatialModeDensity (ℓ : {ℓ : ℝ // 0 < ℓ}) {k : Fin 3 → ℕ}
    (hk : ∀ i, 0 < k i) : (∫ x, spatialModeDensity ℓ k x ∂cubeCoordinateMeasure ℓ) = 1 := by
  unfold spatialModeDensity cubeCoordinateMeasure
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_eq_one
  intro i _
  exact integral_dirichletFactorDensity ℓ (hk i)

theorem integral_filledDensity {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) (hs : ∀ p ∈ s, IsDirichletIndex p) :
    (∫ x, filledDensity ℓ s x ∂cubeCoordinateMeasure ℓ) = s.card := by
  unfold filledDensity
  rw [integral_finsetSum s (fun p _ => integrable_spatialModeDensity ℓ p.1)]
  calc
    _ = ∑ _ ∈ s, (1 : ℝ) := Finset.sum_congr rfl fun p hp =>
      integral_spatialModeDensity ℓ (hs p hp)
    _ = _ := by simp

theorem integrable_spatialModeDensity_mul (ℓ : {ℓ : ℝ // 0 < ℓ}) (k l : Fin 3 → ℕ) :
    Integrable (fun x => spatialModeDensity ℓ k x * spatialModeDensity ℓ l x)
      (cubeCoordinateMeasure ℓ) := by
  simp only [spatialModeDensity, ← Finset.prod_mul_distrib]
  unfold cubeCoordinateMeasure
  apply Integrable.fintype_prod (f := fun i x => dirichletFactorDensity ℓ (k i) x *
    dirichletFactorDensity ℓ (l i) x)
  intro i
  have hc : Continuous (fun x => dirichletFactorDensity ℓ (k i) x *
      dirichletFactorDensity ℓ (l i) x) := by
    unfold dirichletFactorDensity
    fun_prop
  exact (hc.intervalIntegrable 0 ℓ.val).1

/-- Exact overlap of three-dimensional mode densities. A shared coordinate
contributes the factor `3/2`, even when the spin labels differ. -/
theorem integral_spatialModeDensity_mul (ℓ : {ℓ : ℝ // 0 < ℓ})
    {k l : Fin 3 → ℕ} (hk : ∀ i, 0 < k i) (hl : ∀ i, 0 < l i) :
    (∫ x, spatialModeDensity ℓ k x * spatialModeDensity ℓ l x ∂cubeCoordinateMeasure ℓ) =
      ∏ i, if k i = l i then 3 / (2 * ℓ.val) else 1 / ℓ.val := by
  classical
  simp only [spatialModeDensity, ← Finset.prod_mul_distrib]
  rw [cubeCoordinateMeasure, integral_fintype_prod_eq_prod (fun i x =>
    dirichletFactorDensity ℓ (k i) x * dirichletFactorDensity ℓ (l i) x)]
  apply Finset.prod_congr rfl
  intro i _
  have heq (x : ℝ) : dirichletFactorDensity ℓ (k i) x * dirichletFactorDensity ℓ (l i) x =
      dirichletIntervalMode ℓ ⟨k i, hk i⟩ x ^ 2 *
        dirichletIntervalMode ℓ ⟨l i, hl i⟩ x ^ 2 := by
    exact congrArg₂ (· * ·) (dirichletFactorDensity_eq_sq ℓ (⟨k i, hk i⟩ : ℕ+) x)
      (dirichletFactorDensity_eq_sq ℓ (⟨l i, hl i⟩ : ℕ+) x)
  simp_rw [heq]
  rw [← intervalIntegral.integral_of_le ℓ.property.le]
  have h := integral_dirichletIntervalMode_sq_mul_sq ℓ
    (⟨k i, hk i⟩ : ℕ+) (⟨l i, hl i⟩ : ℕ+)
  split_ifs at h with heq
  · have heq' : k i = l i := congrArg (fun n : ℕ+ => (n : ℕ)) heq
    simpa only [ite_eq_left heq'] using h
  · have heq' : k i ≠ l i := fun hkl => heq (PNat.eq hkl)
    simpa only [ite_eq_right heq'] using h

end LiebThirring.TFLattice

end
