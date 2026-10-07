/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterMarginalsWeighted
public import LiebThirring.Kinetic.PauliLiftEncoding

/-! # Exact orbital contractions on ordered two-particle fibers -/

public section
open MeasureTheory WithLp
open scoped Classical
namespace LiebThirring

theorem slater_prod_eq_two_mul_prod_compl {α M : Type*} [Fintype α] [DecidableEq α]
    [CommMonoid M] (f : α → M) (i k : α) (hik : i ≠ k) :
    (∏ j : α, f j) = (f i * f k) * ∏ j : {j : α // j ≠ i ∧ j ≠ k}, f j := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (a := k) (Finset.univ.erase i) f (by simp [hik.symm]),
    ← mul_assoc]
  congr 1
  exact Finset.prod_subtype _ (by simp [and_comm]) f

theorem particlePosition_insertParticlePair_left {N : ℕ} (i k : Fin N)
    (x y : Position) (Z : OtherPairConfiguration i k) :
    particlePosition (insertParticlePair i k x y Z) i = x := by
  ext a
  simp only [particlePosition, insertParticlePair, PiLp.toLp_apply, ↓reduceDIte]

theorem particlePosition_insertParticlePair_right {N : ℕ} (i k : Fin N) (hik : i ≠ k)
    (x y : Position) (Z : OtherPairConfiguration i k) :
    particlePosition (insertParticlePair i k x y Z) k = y := by
  ext a
  simp only [particlePosition, insertParticlePair, PiLp.toLp_apply, hik.symm, ↓reduceDIte]

theorem orbitalBlockPosition_insertParticlePair {N : ℕ} (i k : Fin N)
    (x y : Position) (Z : OtherPairConfiguration i k)
    (j : {j : Fin N // j ≠ i ∧ j ≠ k}) :
    particlePosition (insertParticlePair i k x y Z) j = orbitalBlockPosition Z j := by
  ext a
  simp only [particlePosition, insertParticlePair, orbitalBlockPosition, PiLp.toLp_apply,
    j.property.1, j.property.2, ↓reduceDIte]

/-- The exact spectator integration with two selected physical positions. -/
theorem integral_orbitalContraction_insertParticlePair {N q : ℕ}
    (u v : Fin N → State 1 q) (i k : Fin N) (hik : i ≠ k) (x y : Position) :
    (∫ Z : OtherPairConfiguration i k, ∏ j : Fin N,
      orbitalContraction (u j) (v j) (particlePosition (insertParticlePair i k x y Z) j)) =
      (orbitalContraction (u i) (v i) x * orbitalContraction (u k) (v k) y) *
        ∏ j : {j : Fin N // j ≠ i ∧ j ≠ k}, inner ℂ (u j) (v j) := by
  simp_rw [slater_prod_eq_two_mul_prod_compl (i := i) (k := k) (hik := hik),
    particlePosition_insertParticlePair_left, particlePosition_insertParticlePair_right i k hik,
    orbitalBlockPosition_insertParticlePair]
  rw [integral_const_mul]
  exact congrArg (fun r : ℂ =>
    (orbitalContraction (u i) (v i) x * orbitalContraction (u k) (v k) y) * r)
    (integral_prod_orbitalContraction_fintype
      (fun j : {j : Fin N // j ≠ i ∧ j ≠ k} => u j) (fun j => v j))

theorem integrable_orbitalContraction_insertParticlePair {N q : ℕ}
    (u v : Fin N → State 1 q) (i k : Fin N) (hik : i ≠ k) (x y : Position) :
    Integrable (fun Z : OtherPairConfiguration i k => ∏ j : Fin N,
      orbitalContraction (u j) (v j) (particlePosition (insertParticlePair i k x y Z) j)) := by
  simp_rw [slater_prod_eq_two_mul_prod_compl (i := i) (k := k) (hik := hik),
    particlePosition_insertParticlePair_left, particlePosition_insertParticlePair_right i k hik,
    orbitalBlockPosition_insertParticlePair]
  exact (integrable_prod_orbitalContraction_fintype
    (fun j : {j : Fin N // j ≠ i ∧ j ≠ k} => u j) (fun j => v j)).const_mul _

end LiebThirring
end
