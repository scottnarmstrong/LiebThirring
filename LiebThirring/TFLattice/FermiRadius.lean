/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OccupationRadius
public import LiebThirring.ThomasFermi.KineticConstant
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Equal-mass Fermi radius and sharp kinetic normalization

The radius coefficient depends only on fixed spin multiplicity. Exact algebra
matches the −Δ constant in tfKineticConstant. Source: Lieb–Simon (1977)
III.13, pp. 67–69 (sharp eigenvalue sums), with the kinetic normalization in the TF argument.
-/

@[expose] public section

namespace LiebThirring.TFLattice

noncomputable def fermiRadiusCoefficient (q : ℕ) : ℝ :=
  (6 / ((q : ℝ) * Real.pi)) ^ (1 / 3 : ℝ)

noncomputable def fermiRadius (q n : ℕ) : ℝ :=
  fermiRadiusCoefficient q * (n : ℝ) ^ (1 / 3 : ℝ)

theorem fermiRadiusCoefficient_nonneg (q : ℕ) : 0 ≤ fermiRadiusCoefficient q := by
  exact Real.rpow_nonneg (by positivity) _

theorem fermiRadius_nonneg (q n : ℕ) : 0 ≤ fermiRadius q n :=
  mul_nonneg (fermiRadiusCoefficient_nonneg q) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem cube_root_pow (n : ℕ) (k : ℕ) :
    ((n : ℝ) ^ (1 / 3 : ℝ)) ^ k = (n : ℝ) ^ ((k : ℝ) / 3) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  ring

theorem fermiRadiusCoefficient_cubed {q : ℕ} (hq : 0 < q) :
    fermiRadiusCoefficient q ^ 3 = 6 / ((q : ℝ) * Real.pi) := by
  unfold fermiRadiusCoefficient
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

theorem fermiRadius_mass {q : ℕ} (hq : 0 < q) (n : ℕ) :
    (q : ℝ) * (Real.pi / 6 * fermiRadius q n ^ 3) = n := by
  unfold fermiRadius
  rw [mul_pow, fermiRadiusCoefficient_cubed hq, cube_root_cubed]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

theorem fermiRadiusCoefficient_kinetic {q : ℕ} (hq : 1 ≤ q) :
    Real.pi ^ 2 * ((q : ℝ) * (Real.pi / 10) * fermiRadiusCoefficient q ^ 5) =
      (tfKineticConstant ⟨q, hq⟩).val := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hc := fermiRadiusCoefficient_cubed hq
  have hp : (Real.pi ^ 3) ^ (2 / 3 : ℝ) = Real.pi ^ 2 := by
    rw [← Real.rpow_natCast_mul Real.pi_pos.le 3 (2 / 3 : ℝ)]
    norm_num
  have hs : fermiRadiusCoefficient q ^ 2 =
      (6 / ((q : ℝ) * Real.pi)) ^ (2 / 3 : ℝ) := by
    unfold fermiRadiusCoefficient
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hsq : Real.pi ^ 2 * fermiRadiusCoefficient q ^ 2 =
      (6 * Real.pi ^ 2 / (q : ℝ)) ^ (2 / 3 : ℝ) := by
    calc
      _ = (Real.pi ^ 3) ^ (2 / 3 : ℝ) *
          (6 / ((q : ℝ) * Real.pi)) ^ (2 / 3 : ℝ) := by rw [hp, hs]
      _ = _ := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        field_simp
  have hfive : fermiRadiusCoefficient q ^ 5 =
      fermiRadiusCoefficient q ^ 3 * fermiRadiusCoefficient q ^ 2  := by ring!
  change _ = (3 / 5 : ℝ) * (6 * Real.pi ^ 2 / (q : ℝ)) ^ (2 / 3 : ℝ)
  rw [hfive, hc, ← hsq]
  field_simp
  ring

theorem fermiRadius_kinetic {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    Real.pi ^ 2 * ((q : ℝ) * (Real.pi / 10) * fermiRadius q n ^ 5) =
      (tfKineticConstant ⟨q, hq⟩).val * (n : ℝ) ^ (5 / 3 : ℝ) := by
  unfold fermiRadius
  rw [mul_pow, cube_root_pow]
  calc
    _ = (Real.pi ^ 2 * ((q : ℝ) * (Real.pi / 10) * fermiRadiusCoefficient q ^ 5)) *
        (n : ℝ) ^ (5 / 3 : ℝ)  := by ring!
    _ = _ := by rw [fermiRadiusCoefficient_kinetic hq]

end LiebThirring.TFLattice

end
