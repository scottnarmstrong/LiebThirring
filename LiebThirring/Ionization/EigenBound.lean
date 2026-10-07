/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.PairInequality
public import LiebThirring.Ionization.StrictExpectations

/-! # The weak-eigenfunction bound at the escape threshold

The threshold inequality may be equality. No position moment
or pointwise eigenfunction equation is required.
-/

public section
open MeasureTheory
open scoped NNReal
namespace LiebThirring

/-- The strict pair-count inequality implies the numerical electron bound. -/
theorem electron_count_lt_of_pair_count_lt {n Z : ℝ} (hn : 0 < n)
    (h : n * (n - 1) / 2 < n * Z) : n < 2 * Z + 1 := by
  nlinarith only [h, hn]

/-- Every normalized atomic weak eigenfunction below the escape threshold satisfies the strict electron-count bound.
The vacuum case is included; positive spin count is not needed for this implication. -/
theorem electron_count_lt_of_atomic_weak_eigenfunction {N q : ℕ}
    (Z : ℝ≥0) (hZ : 0 < Z) (E : ℝ) (u : FormDomain N q)
    (hu : ‖(u : State N q)‖ = 1)
    (heig : is_weak_eigenfunction (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) E u)
    (hE : E ≤ (atomicGroundStateEnergy (N - 1) q Z).toReal) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 := by
  have hZr : 0 < (Z : ℝ) := hZ
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    simp only [Nat.cast_zero]
    positivity
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  by_cases hn : n = 0
  · subst n
    norm_num only [Nat.zero_add, Nat.cast_one]
    linarith only [hZr]
  have htwo : 2 ≤ n + 1 := by omega
  have hp := pair_count_lt_of_ionization_cutoff htwo (u : State (n + 1) q) hu
    (((n + 1 : ℕ) : ℝ) * Z)
    (fun ε hε i j hij => by
      simpa only [ionizationPairCutoff, ionizationParticleWeight] using
        integrable_ionization_pair_density ε hε i j (ne_of_lt hij) u)
    (fun ε hε => by
      simpa only [ionizationPairCutoff] using
        ionization_cutoff_pair_sum_le Z E u hu heig.2
          (by simpa only [Nat.succ_sub_one] using hE) ε hε)
  exact electron_count_lt_of_pair_count_lt (by exact_mod_cast hN) hp

end LiebThirring
end
