/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OccupationRadius
public import LiebThirring.TFLattice.SpatialBall

/-!
# Finite occupation comparison and a uniform radius estimate

The occupation order allows arbitrary choices in an equal-energy last shell.
The coarse radius bound uses a cube count, not an asymptotic lattice theorem.
Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

public section

namespace LiebThirring.TFLattice

theorem sum_squaredRadius_le_of_isFilled {q : ℕ} {admissible : ModeIndex q → Prop}
    {s t : Finset (ModeIndex q)} (hs : IsFilled admissible s)
    (ht : ∀ p ∈ t, admissible p) (hc : s.card = t.card) :
    (∑ p ∈ s, (squaredRadius p.1 : ℝ)) ≤ ∑ p ∈ t, (squaredRadius p.1 : ℝ) := by
  classical
  let e := Finset.equivOfCardEq (Finset.card_sdiff_comm hc)
  have hd : (∑ p ∈ s \ t, (squaredRadius p.1 : ℝ)) ≤
      ∑ p ∈ t \ s, (squaredRadius p.1 : ℝ) := by
    rw [← Finset.sum_coe_sort (s \ t), ← Finset.sum_coe_sort (t \ s)]
    calc
      _ ≤ ∑ p : ↥(s \ t), (squaredRadius (e p).val.1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        have hp := Finset.mem_sdiff.mp p.property
        have hr := Finset.mem_sdiff.mp (e p).property
        exact_mod_cast hs.2 p hp.1 (e p) (ht _ hr.1) hr.2
      _ = _ := e.sum_comp (fun p : ↥(t \ s) => (squaredRadius p.val.1 : ℝ))
  have hdiff := Finset.sum_sdiff_sub_sum_sdiff (s₁ := t) (s₂ := s)
    (f := fun p => (squaredRadius p.1 : ℝ))
  linarith

theorem neumann_occupation_radius_le {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s)
    (hn : 1 ≤ s.card) {p : ModeIndex q} (hp : p ∈ s) :
    ‖latticeCorner 1 (unitCellLabel p.1)‖ ≤
      6 * (s.card : ℝ) ^ (1 / 3 : ℝ) := by
  let m := ⌈(s.card : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1
  have hrad := squaredRadius_le_of_isFilled hs
    (a := 0) (m := m) (fun _ _ => trivial) (card_lt_comparison_box hq s.card) hp
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg s.card) (1 / 3 : ℝ))
  have hu : 1 ≤ (s.card : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hm : (m : ℝ) ≤ 3 * (s.card : ℝ) ^ (1 / 3 : ℝ) := by
    dsimp [m]
    push_cast
    linarith
  have hsq : ‖latticeCorner 1 (unitCellLabel p.1)‖ ^ 2 ≤ 3 * (m : ℝ) ^ 2 := by
    rw [norm_unitCellCorner_sq]
    exact_mod_cast (show squaredRadius p.1 ≤ 3 * m ^ 2 by
      simpa only [zero_add] using hrad)
  have hm2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm 2
  have hn0 := norm_nonneg (latticeCorner 1 (unitCellLabel p.1))
  have hu0 := Real.rpow_nonneg (Nat.cast_nonneg s.card) (1 / 3 : ℝ)
  nlinarith only [hsq, hm2, hn0, hu0]

end LiebThirring.TFLattice

end
