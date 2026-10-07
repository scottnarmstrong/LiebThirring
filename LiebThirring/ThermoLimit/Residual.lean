/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.BallLattice
import Mathlib.Tactic

/-!
# Deterministic residual multiplets and the vacuum-density bound

Coupled integer interpolation's optional residual construction uses the actual interior lattice
count from lattice boundary estimates, with the same geometric boundary bound. The energy is an abstract
neutral-sector ball energy. The only physical inputs are integer neutral
packing and extensive stability.
-/

public section

open Filter Topology Metric Set Finset

namespace LiebThirring.ThermoLimit

/-- Unit balls selected from the eligible side-two cells fill any count below
the actual grid capacity, at a cost linear in that count. -/
theorem residual_energy_le {F : ℝ → ℕ → ℝ} {C L : ℝ} {r : ℕ}
    (hpacking : ∀ (s : Finset LatticeIndex) (m : LatticeIndex → ℕ),
      (∀ i ∈ s, ball (latticeCenter 2 i) 1 ⊆ ball (0 : Position) L) →
      (s : Set LatticeIndex).PairwiseDisjoint (fun i => ball (latticeCenter 2 i) 1) →
      F L (∑ i ∈ s, m i) ≤ ∑ i ∈ s, F 1 (m i))
    (htrial : F 1 1 ≤ C)
    (hcapacity : r ≤ ballLatticeCount 2 L (by norm_num)) :
    F L r ≤ C * r := by
  classical
  let cells := interiorLatticeCubes 2 (ball (0 : Position) L) (by norm_num) isBounded_ball
  have hcap : r ≤ cells.card := hcapacity
  obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq hcap
  have hsub : ∀ i ∈ s, ball (latticeCenter 2 i) 1 ⊆ ball (0 : Position) L := by
    intro i hi
    simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
      interior_lattice_ball_subset (hs hi)
  have hd : (s : Set LatticeIndex).PairwiseDisjoint
      (fun i => ball (latticeCenter 2 i) 1) := by
    intro i _ j _ hij
    simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
      lattice_inscribed_balls_pairwiseDisjoint (by norm_num : (0 : ℝ) < 2) hij
  have hp := hpacking s (fun _ => 1) hsub hd
  simp only [sum_const, nsmul_eq_mul, Nat.mul_one, hcard] at hp
  exact hp.trans (by nlinarith only [htrial, (Nat.cast_nonneg r : (0 : ℝ) ≤ r)])

/-- An `o(volume)` residual fits into the actual unit-ball lattice eventually. -/
theorem eventually_residual_le_ballLatticeCount {L : ℕ → ℝ} {r : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hr : Tendsto (fun n => (r n : ℝ) / (ballVolumeConstant * L n ^ 3)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, r n ≤ ballLatticeCount 2 (L n) (by norm_num) := by
  have hc : Tendsto (fun n => (ballLatticeCount 2 (L n) (by norm_num) : ℝ) /
      (ballVolumeConstant * L n ^ 3)) atTop (𝓝 (1 / 8 : ℝ)) := by
    have ht := (tendsto_ballLatticeCount_normalized 2 (by norm_num)).comp hL
    convert ht.div_const 8 using 1
    norm_num
    ext n
    ring
  filter_upwards [hL.eventually (eventually_gt_atTop 0),
    hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hc.eventually (lt_mem_nhds (by norm_num : (1 / 16 : ℝ) < 1 / 8))] with n hLn hrn hcn
  have hv : 0 < ballVolumeConstant * L n ^ 3 := mul_pos ballVolumeConstant_pos (pow_pos hLn _)
  have hreal : (r n : ℝ) < ballLatticeCount 2 (L n) (by norm_num) :=
    (div_lt_div_iff_of_pos_right hv).mp (hrn.trans hcn)
  exact le_of_lt (by exact_mod_cast hreal)

end LiebThirring.ThermoLimit

end
