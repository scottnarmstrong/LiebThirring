/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.CoordinateCollisions
public import LiebThirring.TFLattice.FilledModes
import Mathlib.Tactic

/-!
# Actual radial lattice selections

These finite sets count lattice sites in an octant ball, with q-fold spin.
Their membership lemmas remove the finite bounding box entirely. The
Dirichlet–Neumann discrepancy lies on three coordinate faces and has a
quadratic cardinal bound. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).

This module does not assert the sharp ball volume or moment asymptotics.
-/

@[expose] public section

namespace LiebThirring.TFLattice

open scoped NNReal

noncomputable def neumannBallModes (q : ℕ) (t : ℝ≥0) : Finset (ModeIndex q) := by
  classical
  exact (modeBox q 0 (⌊(t : ℝ)⌋₊ + 1)).filter fun p => (squaredRadius p.1 : ℝ) ≤ (t : ℝ) ^ 2

theorem mem_neumannBallModes {q : ℕ} {t : ℝ≥0} {p : ModeIndex q} :
    p ∈ neumannBallModes q t ↔ (squaredRadius p.1 : ℝ) ≤ (t : ℝ) ^ 2 := by
  classical
  simp only [neumannBallModes, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  apply mem_modeBox.mpr
  intro i
  have hcoord : (p.1 i : ℝ) ^ 2 ≤ (squaredRadius p.1 : ℝ) := by
    exact_mod_cast coordinate_sq_le_squaredRadius p.1 i
  have hi : (p.1 i : ℝ) ≤ t := by
    nlinarith [NNReal.coe_nonneg t, (Nat.cast_nonneg (p.1 i) : (0 : ℝ) ≤ p.1 i)]
  have hfloor : p.1 i ≤ ⌊(t : ℝ)⌋₊ := (Nat.le_floor_iff (NNReal.coe_nonneg t)).mpr hi
  exact ⟨Nat.zero_le _, by omega⟩

end LiebThirring.TFLattice

end
