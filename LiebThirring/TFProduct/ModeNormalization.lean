/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes
public import LiebThirring.TFSectors.ProductModes

/-! # Agreement of the cube and sector mode normalizations -/

@[expose] public section

open scoped BigOperators

namespace LiebThirring.TFProduct

open LiebThirring TFCubes TFLattice TFSectors

noncomputable section

private theorem neumannIntervalCoefficient_eq
    (ℓ : {x : ℝ // 0 < x}) (n : ℕ) :
    neumannIntervalCoefficient ℓ n =
      (Real.sqrt ℓ.val)⁻¹ * if n = 0 then 1 else Real.sqrt 2 := by
  by_cases hn : n = 0
  · simp [neumannIntervalCoefficient, hn]
  · simp only [neumannIntervalCoefficient, hn, ↓reduceIte]
    rw [Real.sqrt_div (by positivity : 0 ≤ (2 : ℝ)) ℓ.val]
    rw [div_eq_mul_inv, mul_comm]

private theorem sqrt_inv_cube_eq_rpow (ℓ : {x : ℝ // 0 < x}) :
    (Real.sqrt ℓ.val)⁻¹ ^ (3 : ℕ) = ℓ.val ^ (-(3 : ℝ) / 2) := by
  rw [inv_pow, show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
    Real.rpow_neg ℓ.property.le]
  congr 1
  rw [show (3 : ℝ) / 2 = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
    Real.sqrt_eq_rpow, Real.rpow_mul_natCast ℓ.property.le]

/-- The normalized scalar cosine product used by the cube construction is the
literal scalar factor used by an assigned sector. -/
theorem neumannCubeSpatialMode_latticeCorner
    (ℓ : {x : ℝ // 0 < x}) (β : LatticeIndex) (k : Fin 3 → ℕ) (x : Position) :
    neumannCubeSpatialMode ℓ (latticeCorner ℓ.val β) k x =
      (ℓ.val ^ (-(3 : ℝ) / 2) * ∏ a : Fin 3,
        (if k a = 0 then 1 else Real.sqrt 2) *
          Real.cos (Real.pi * (k a : ℝ) *
            (x a - ℓ.val * (β a : ℝ)) / ℓ.val) : ℝ) := by
  unfold neumannCubeSpatialMode
  rw [← Complex.ofReal_prod]
  congr 1
  simp only [neumannIntervalMode, neumannIntervalCoefficient_eq,
    intervalFrequency, latticeCorner, PiLp.toLp_apply]
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const, Finset.card_fin, sqrt_inv_cube_eq_rpow]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  congr 2
  ring

/-- The one-particle mode used by the physical cube basis agrees pointwise
with the mode used in the ordered-assignment sector. -/
theorem neumannCubeModeValue_latticeCorner {q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (β : LatticeIndex) (p : ModeIndex q)
    (x : Position) (s : Fin q) :
    neumannCubeModeValue ℓ (latticeCorner ℓ.val β) p x s =
      neumannModeValue ℓ β p x s := by
  rw [neumannCubeModeValue_apply]
  unfold neumannModeValue
  by_cases hs : s = p.2
  · simp only [hs, ↓reduceIte, neumannCubeSpatialMode_latticeCorner]
  · simp only [hs, ↓reduceIte]

/-- The sector product mode is a scalar spatial product in the single global
spin component selected by the one-particle mode labels. -/
theorem neumannProductMode_eq_single_cubeSpatialMode {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (k : Fin N → ModeIndex q) (x : Configuration N) :
    neumannProductMode ℓ b k x =
      EuclideanSpace.single (fun i => (k i).2)
        (∏ i : Fin N, neumannCubeSpatialMode ℓ
          (latticeCorner ℓ.val (b i)) (k i).1 (particlePosition x i)) := by
  classical
  apply PiLp.ext
  intro s
  rw [neumannProductMode, PiLp.toLp_apply, PiLp.single_apply]
  by_cases hs : s = fun i => (k i).2
  · simp only [hs, ↓reduceIte]
    apply Finset.prod_congr rfl
    intro i _
    rw [← neumannCubeModeValue_latticeCorner]
    simp only [neumannCubeModeValue_apply, ↓reduceIte]
  · simp only [hs, ↓reduceIte]
    have hmismatch : ∃ i, s i ≠ (k i).2 := by
      by_contra h
      apply hs
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmismatch
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [← neumannCubeModeValue_latticeCorner]
    simp only [neumannCubeModeValue_apply, hi, ↓reduceIte]

end

end LiebThirring.TFProduct

end
