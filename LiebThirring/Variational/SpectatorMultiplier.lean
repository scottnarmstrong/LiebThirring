/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.LipschitzProductRule
public import LiebThirring.Variational.SpectatorForm

/-!
# A selected-coordinate multiplier has no spectator derivative

These spectator disintegration product-rule lemmas make no antisymmetry claim about the multiplied
state. The vanishing derivative follows from constancy on the coordinate
line, including points at which the total derivative is defined to be zero.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring
open Sobolev

/-- Projection to a particle position is a contraction for the Euclidean norm. -/
theorem lipschitzWith_particlePosition {N : ℕ} (i : Fin N) :
    LipschitzWith 1 (fun X : Configuration N => particlePosition X i) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have hsub : particlePosition X i - particlePosition Y i = particlePosition (X - Y) i := by
    ext a
    rfl
  rw [hsub]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, particlePosition]
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum
    (fun j _ => Finset.sum_nonneg (fun a _ => sq_nonneg ((X - Y) (j, a))))
    (Finset.mem_univ i)

/-- A Lipschitz one-particle multiplier lifts with exactly the same Lipschitz constant. -/
theorem lipschitzWith_selected_multiplier {N : ℕ} (i : Fin N)
    (b : Position → ℝ) (C : ℝ≥0) (hb : LipschitzWith C b) :
    LipschitzWith C (fun X : Configuration N => b (particlePosition X i)) := by
  simpa only [mul_one, Function.comp_def] using hb.comp (lipschitzWith_particlePosition i)

/-- A coordinate vector of a different particle does not change the selected position. -/
theorem particlePosition_add_coordinateVector_other {N : ℕ} (i j : Fin N)
    (hji : j ≠ i) (a : Fin 3) (X : Configuration N) (t : ℝ) :
    particlePosition (X + t • coordinateVector (j, a)) i = particlePosition X i := by
  ext c
  simp [particlePosition, coordinateVector, EuclideanSpace.basisFun_apply, Ne.symm hji]

/-- The total selected multiplier derivative vanishes in every spectator coordinate. -/
theorem lipschitzDirectionalDerivative_selected_other {N : ℕ} (i j : Fin N)
    (hji : j ≠ i) (a : Fin 3) (b : Position → ℝ) (X : Configuration N) :
    lipschitzDirectionalDerivative (fun Y => b (particlePosition Y i)) (j, a) X = 0 := by
  have hline : HasLineDerivAt ℝ (fun Y : Configuration N => b (particlePosition Y i))
      0 X (coordinateVector (j, a)) := by
    change HasDerivAt (fun t : ℝ => b (particlePosition (X + t • coordinateVector (j, a)) i)) 0 0
    simp only [particlePosition_add_coordinateVector_other i j hji]
    exact hasDerivAt_const 0 _
  unfold lipschitzDirectionalDerivative
  by_cases hx : DifferentiableAt ℝ (fun Y : Configuration N => b (particlePosition Y i)) X
  · exact (hx.hasFDerivAt.hasLineDerivAt _).unique hline
  · rw [fderiv_zero_of_not_differentiableAt hx]
    rfl

/-- A spectator weak derivative of the selected-coordinate product is the
multiplier times the original weak derivative. -/
theorem hasWeakDerivative_selected_multiplier_other {N q : ℕ} (i j : Fin N)
    (hji : j ≠ i) (a : Fin 3) (u : State N q)
    (g : (Fin N × Fin 3) → State N q)
    (hu : ∀ c, HasWeakDerivative c u (g c))
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C (fun X : Configuration N => b (particlePosition X i))) :
    HasWeakDerivative (j, a)
      (lipschitzBoundedSMul (fun X => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) hb u)
      (lipschitzBoundedSMul (fun X => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) hb
        (g (j, a))) := by
  have h := hasWeakDerivative_lipschitz_product u g hu
    (fun X => b (particlePosition X i)) B (fun X => hB _) C hb (j, a)
  have heq : lipschitzProductDerivative (fun X => b (particlePosition X i))
      B (fun X => hB _) C hb (j, a) u (g (j, a)) =
      lipschitzBoundedSMul (fun X => b (particlePosition X i))
        B (fun X => hB _) hb (g (j, a)) := by
    apply Lp.ext
    filter_upwards [lipschitzProductDerivative_coeFn (fun X => b (particlePosition X i))
      B (fun X => hB _) C hb (j, a) u (g (j, a)),
      lipschitzBoundedSMul_coeFn (fun X => b (particlePosition X i))
        B (fun X => hB _) hb (g (j, a))] with X hx hy
    rw [hx, hy, lipschitzDirectionalDerivative_selected_other i j hji,
      Complex.ofReal_zero, zero_smul, add_zero]
  rwa [heq] at h

end LiebThirring
end
