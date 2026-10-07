/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterBasic
import LiebThirring.Kinetic.DensityBasic

/-! # Spatial density and exchange kernel of a finite orbital family

The orbitals retain their full complex spatial-spin dependence. The pointwise
exchange estimate holds for every finite family, before imposing orthonormality.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal ComplexConjugate
namespace LiebThirring

theorem continuous_oneParticleConfiguration : Continuous oneParticleConfiguration := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 × Fin 3 => ℝ)).comp
    (continuous_pi fun ia => PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ia.2)

theorem measurable_orbitalValue {q : ℕ} (u : State 1 q) (s : Fin q) :
    Measurable (fun x => orbitalValue u x s) := by
  exact (PiLp.continuous_apply 2 (fun _ : SpinLabels 1 q => ℂ)
    (oneParticleSpinLabel s)).measurable.comp
      ((Lp.stronglyMeasurable u).measurable.comp continuous_oneParticleConfiguration.measurable)

/-- The spatial density prescribed by the occupied orbitals. -/
@[expose] noncomputable def slaterOrbitalDensity {N q : ℕ}
    (u : Fin N → State 1 q) (x : Position) : ℝ :=
  ∑ s : Fin q, ∑ j : Fin N, ‖orbitalValue (u j) x s‖ ^ 2

/-- The integral kernel of the finite-rank spatial-spin projector. -/
@[expose] noncomputable def slaterDensityMatrix {N q : ℕ}
    (u : Fin N → State 1 q) (x y : Position) (s t : Fin q) : ℂ :=
  ∑ j : Fin N, orbitalValue (u j) x s * conj (orbitalValue (u j) y t)

/-- The spin-summed modulus-square appearing in the exchange term. -/
@[expose] noncomputable def slaterExchangeDensity {N q : ℕ}
    (u : Fin N → State 1 q) (x y : Position) : ℝ :=
  ∑ s : Fin q, ∑ t : Fin q, ‖slaterDensityMatrix u x y s t‖ ^ 2

theorem slaterOrbitalDensity_nonneg {N q : ℕ} (u : Fin N → State 1 q)
    (x : Position) : 0 ≤ slaterOrbitalDensity u x := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem slaterExchangeDensity_nonneg {N q : ℕ} (u : Fin N → State 1 q)
    (x y : Position) : 0 ≤ slaterExchangeDensity u x y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The orbital spatial density is the sum of the full spin-vector squared norms. -/
theorem slaterOrbitalDensity_eq_sum_norm_sq {N q : ℕ} (u : Fin N → State 1 q)
    (x : Position) :
    slaterOrbitalDensity u x = ∑ j : Fin N, ‖u j (oneParticleConfiguration x)‖ ^ 2 := by
  unfold slaterOrbitalDensity
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let e : Fin q ≃ SpinLabels 1 q :=
    { toFun := oneParticleSpinLabel
      invFun := fun s => s 0
      left_inv := fun _ => rfl
      right_inv := fun s => by funext i; exact congrArg s (Subsingleton.elim 0 i) }
  rw [PiLp.norm_sq_eq_of_L2, ← e.sum_comp]
  rfl

end LiebThirring
end
