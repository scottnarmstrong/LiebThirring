/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterCoulomb
public import LiebThirring.TFQuantum.SlaterProduct
public import LiebThirring.Kinetic.FourierFactor
import LiebThirring.Variational.FormCoulombSlices
import LiebThirring.Electrostatics.Gaussian

/-! # Coulomb finiteness from finite orbital kinetic energy

Hardy's one-particle estimate bounds each orbital potential uniformly in its
pole. Integrating against another orbital's finite mass proves direct Coulomb
finiteness for arbitrary finite-kinetic orbital families.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

theorem ofReal_slaterOrbitalDensity {N q : ℕ} (u : Fin N → State 1 q)
    (x : Position) :
    ENNReal.ofReal (slaterOrbitalDensity u x) =
      ∑ j : Fin N, (‖u j (oneParticleConfiguration x)‖₊ : ℝ≥0∞) ^ 2 := by
  rw [slaterOrbitalDensity_eq_sum_norm_sq,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  rw [ofReal_norm, enorm_eq_nnnorm]

end LiebThirring
end
