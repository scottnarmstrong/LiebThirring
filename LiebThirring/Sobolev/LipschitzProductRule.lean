/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.LipschitzScalarWeak
public import LiebThirring.Kinetic.DensityBasic

/-! # Bounded Lipschitz spatial multipliers preserve the kinetic form domain -/

public section

open MeasureTheory WithLp
open scoped NNReal ENNReal

namespace LiebThirring.Sobolev

/-- The spatial weak product rule on every coordinate of a finite-energy state. -/
theorem hasWeakDerivative_lipschitz_product {N q : ℕ} (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hu : ∀ a, HasWeakDerivative a u (g a))
    (b : Configuration N → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (C : ℝ≥0) (hb : LipschitzWith C b) :
    ∀ a, HasWeakDerivative a (lipschitzBoundedSMul b B hB hb u)
      (lipschitzProductDerivative b B hB C hb a u (g a)) := by
  let bc := fun x => (b x : ℂ)
  let dc := fun a x => (lipschitzDirectionalDerivative b a x : ℂ)
  have hbmeas : AEStronglyMeasurable bc :=
    (Complex.measurable_ofReal.comp hb.continuous.measurable).aestronglyMeasurable
  have hdmeas (a) : AEStronglyMeasurable (dc a) :=
    (Complex.measurable_ofReal.comp (lipschitzDirectionalDerivative_measurable b a)).aestronglyMeasurable
  have hbc (x) : ‖bc x‖ ≤ B := by simpa only [bc, Complex.norm_real] using hB x
  have hdc (a x) : ‖dc a x‖ ≤ (C : ℝ) := by
    simpa only [dc, Complex.norm_real] using norm_lipschitzDirectionalDerivative_le b C hb a x
  have hs := hasWeakDerivative_scalar_weak_product g hu bc dc B (fun _ => (C : ℝ))
    hbc hdc hbmeas hdmeas (fun a => hasScalarWeakDerivative_lipschitz a b C hb)
  have he₀ : boundedSMul bc u B hbc hbmeas = lipschitzBoundedSMul b B hB hb u := by
    apply Lp.ext
    filter_upwards [boundedSMul_coeFn bc u B hbc hbmeas,
      lipschitzBoundedSMul_coeFn b B hB hb u] with x hx hy
    exact hx.trans hy.symm
  intro a
  have he₁ : scalarWeakProductDerivative bc (dc a) B (C : ℝ) hbc (hdc a)
      hbmeas (hdmeas a) u (g a) = lipschitzProductDerivative b B hB C hb a u (g a) := by
    apply Lp.ext
    filter_upwards [scalarWeakProductDerivative_coeFn bc (dc a) B (C : ℝ) hbc (hdc a)
      hbmeas (hdmeas a) u (g a), lipschitzProductDerivative_coeFn b B hB C hb a u (g a)] with x hx hy
    exact hx.trans hy.symm
  simpa only [he₀, he₁] using hs a

/-- Every bounded real Lipschitz spatial multiplier preserves finite kinetic energy. -/
theorem kineticEnergy_lipschitzBoundedSMul_lt_top {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) (b : Configuration N → ℝ)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (C : ℝ≥0) (hb : LipschitzWith C b) :
    kineticEnergy (lipschitzBoundedSMul b B hB hb u) < ⊤ := by
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top u hu
  exact (kineticEnergy_lt_top_iff_exists_weakDerivatives _).mpr
    ⟨fun a => lipschitzProductDerivative b B hB C hb a u (g a),
      hasWeakDerivative_lipschitz_product u g hg b B hB C hb⟩

end LiebThirring.Sobolev

end
