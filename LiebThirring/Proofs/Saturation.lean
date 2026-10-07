/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.RelaxedEnergy
import LiebThirring.TFMinimizer.Saturation

/-!
# Thomas–Fermi saturation and exact-mass attainment

The relaxed minimizer has mass min(ν, Z₀). Excess mass escapes at vanishing cost,
so exact-mass energies saturate at neutrality and attain their infimum precisely for ν ≤ Z₀.
Source: Lieb–Simon (1977), Theorems II.17–II.20 and II.32; Lieb (1981), Theorems 2.5 and 3.18.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem tfEnergy_saturation_and_attainment {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R) :
    tfEnergy a ν z R = tfEnergy a (min ν (∑ k, z k)) z R ∧
      ((∃ ρ : TFDensity, tfMass ρ = (ν : ℝ) ∧
        (tfFunctional a z R ρ : EReal) = tfEnergy a ν z R) ↔ ν ≤ ∑ k, z k) ∧
      (∀ ρ : TFDensity, tfMass ρ ≤ (ν : ℝ) →
        (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R →
          tfMass ρ = ((min ν (∑ k, z k) : ℝ≥0) : ℝ)) :=
  LiebThirring.TFMinimizer.tfEnergy_saturation_and_attainment a ν z hz R hR

end LiebThirring.Proofs

end
