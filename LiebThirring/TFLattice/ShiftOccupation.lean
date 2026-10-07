/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OccupationComparison
public import LiebThirring.TFLattice.FermiRadius
import Mathlib.Tactic

/-!
# Translating Neumann occupations into Dirichlet trials

Adding one to every spatial coordinate preserves distinct spin modes and
costs at most 39 n^(4/3) in the squared-radius sum of a filled occupation.
Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums), unit boundary displacement.
-/

@[expose] public section

namespace LiebThirring.TFLattice

def shiftMode {q : ℕ} (p : ModeIndex q) : ModeIndex q := (fun i => p.1 i + 1, p.2)

theorem shiftMode_injective (q : ℕ) : Function.Injective (shiftMode (q := q)) := by
  intro p r he
  apply Prod.ext
  · funext i
    exact Nat.add_right_cancel (congrFun (congrArg Prod.fst he) i)
  · simpa only [shiftMode] using congrArg Prod.snd he

theorem isDirichletIndex_shiftMode {q : ℕ} (p : ModeIndex q) : IsDirichletIndex (shiftMode p) :=
  fun _ => Nat.succ_pos _

theorem squaredRadius_shiftMode {q : ℕ} (p : ModeIndex q) :
    (squaredRadius (shiftMode p).1 : ℝ) =
      (squaredRadius p.1 : ℝ) + 2 * (∑ i, (p.1 i : ℝ)) + 3 := by
  simp only [squaredRadius, shiftMode, Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  simp_rw [show ∀ i, ((p.1 i : ℝ) + 1) ^ 2 = (p.1 i : ℝ) ^ 2 + 2 * p.1 i + 1 by
    intro i; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem sum_squaredRadius_shiftMode_le {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s) :
    (∑ p ∈ s.image shiftMode, (squaredRadius p.1 : ℝ)) ≤
      (∑ p ∈ s, (squaredRadius p.1 : ℝ)) + 39 * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  rw [Finset.sum_image (fun p _ r _ h => shiftMode_injective q h)]
  by_cases hn : s.card = 0
  · have he := Finset.card_eq_zero.mp hn
    simp [he, Real.zero_rpow (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  have hn1 := Nat.one_le_iff_ne_zero.mpr hn
  let u := (s.card : ℝ) ^ (1 / 3 : ℝ)
  have hu : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hcoord {p : ModeIndex q} (hp : p ∈ s) (i : Fin 3) : (p.1 i : ℝ) ≤ 6 * u := by
    have hs1 := neumann_occupation_radius_le hq hs hn1 hp
    have hs2 : (p.1 i : ℝ) ^ 2 ≤ ‖latticeCorner 1 (unitCellLabel p.1)‖ ^ 2 := by
      rw [norm_unitCellCorner_sq]
      exact_mod_cast coordinate_sq_le_squaredRadius p.1 i
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hs1 2
    have hnon : (0 : ℝ) ≤ (p.1 i : ℝ) := Nat.cast_nonneg _
    nlinarith only [hs2, hsq, hnon, hu]
  have hsum : (∑ p ∈ s, (squaredRadius (shiftMode p).1 : ℝ)) ≤
      ∑ p ∈ s, ((squaredRadius p.1 : ℝ) + 39 * u) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [squaredRadius_shiftMode]
    have hsc : (∑ i, (p.1 i : ℝ)) ≤ 18 * u := by
      calc
        _ ≤ ∑ _i : Fin 3, 6 * u := Finset.sum_le_sum fun i _ => hcoord hp i
        _ = _ := by simp; ring
    linarith only [hsc, hu]
  have he : u * (s.card : ℝ) = (s.card : ℝ) ^ (4 / 3 : ℝ) := by
    calc
      _ = u * u ^ 3 := by rw [cube_root_cubed]
      _ = u ^ 4 := by ring
      _ = _ := cube_root_pow s.card 4
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith only [hsum, he]

end LiebThirring.TFLattice

end
