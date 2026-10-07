/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Cube lattice indices and spin multiplicity

An index carries three nonnegative integer coordinates and one spin label.
The Neumann lattice uses all indices; Dirichlet indices have positive
coordinates. No enumeration chooses a preferred member of a degenerate shell.

Source: Lieb–Simon (1977), III.13, journal pp. 67–69.
-/

@[expose] public section

namespace LiebThirring.TFLattice

abbrev ModeIndex (q : ℕ) := (Fin 3 → ℕ) × Fin q

/-- Squared spatial lattice radius; spin does not change it. -/
def squaredRadius (k : Fin 3 → ℕ) : ℕ := ∑ i, k i ^ 2

/-- The positive-coordinate sublattice for Dirichlet boundary conditions. -/
def IsDirichletIndex {q : ℕ} (p : ModeIndex q) : Prop := ∀ i, 0 < p.1 i

/-- A translated integer box, with all `q` spin labels at each spatial site. -/
def modeBox (q a m : ℕ) : Finset (ModeIndex q) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.Ico a (a + m)) ×ˢ Finset.univ

theorem mem_modeBox {q a m : ℕ} {p : ModeIndex q} :
    p ∈ modeBox q a m ↔ ∀ i, a ≤ p.1 i ∧ p.1 i < a + m := by
  simp [modeBox, Fintype.mem_piFinset]

theorem card_modeBox (q a m : ℕ) : (modeBox q a m).card = q * m ^ 3 := by
  simp [modeBox, Fintype.card_piFinset, Finset.prod_const, mul_comm]

theorem squaredRadius_le_of_mem_modeBox {q a m : ℕ} {p : ModeIndex q}
    (hp : p ∈ modeBox q a m) : squaredRadius p.1 ≤ 3 * (a + m) ^ 2 := by
  have h := mem_modeBox.mp hp
  calc
    squaredRadius p.1 ≤ ∑ _ : Fin 3, (a + m) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (h i).2.le 2
    _ = 3 * (a + m) ^ 2 := by simp

theorem isDirichletIndex_of_mem_modeBox {q a m : ℕ} (ha : 0 < a)
    {p : ModeIndex q} (hp : p ∈ modeBox q a m) : IsDirichletIndex p :=
  fun i => lt_of_lt_of_le ha (mem_modeBox.mp hp i).1

/-- The explicit eigenvalue of `-Δ` in a cube of positive side length `ℓ`.
Cube translation does not occur in this formula. -/
noncomputable def cubeEigenvalue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (p : ModeIndex q) : ℝ := Real.pi ^ 2 * (squaredRadius p.1 : ℝ) / ℓ.val ^ 2

theorem cubeEigenvalue_nonneg {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (p : ModeIndex q) : 0 ≤ cubeEigenvalue ℓ p := by
  unfold cubeEigenvalue
  positivity

end LiebThirring.TFLattice

end
