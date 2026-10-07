/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.KineticLT
public import LiebThirring.Assembly.Screening
public import LiebThirring.ThomasFermi.Density
public import LiebThirring.ThomasFermi.KineticConstant
import LiebThirring.Assembly.Young

/-! # The potential dual of kinetic Lieb–Thirring

Argument nuclear-core estimate (direct proof): the exact Young coefficient pays for an
arbitrary nonnegative measurable potential with a fraction of kinetic energy.
The additive extended estimate precedes every real conversion.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFCore

/-- The real coefficient of the already proved kinetic LT theorem. -/
@[expose] noncomputable def kineticCoefficient (q : ℕ) : ℝ :=
  (ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3)

/-- The sharp scalar Young coefficient for exponents 5/3 and 5/2. -/
@[expose] noncomputable def youngConstant : ℝ :=
  (2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)

theorem kineticCoefficient_pos (q : ℕ) (hq : 1 ≤ q) :
    0 < kineticCoefficient q := Assembly.kinetic_coefficient_pos q hq

/-- Extended LT duality, valid also when kinetic energy is infinite. -/
theorem lintegral_potential_density_le (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (ψ : State N q) (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (η : ℝ) (hη : 0 < η) (v : Position → ℝ≥0∞) :
    (∫⁻ x : Position, v x * density ψ x) ≤
      ENNReal.ofReal η * kineticEnergy ψ +
        ENNReal.ofReal (youngConstant * (η * kineticCoefficient q) ^ (-(3 : ℝ) / 2)) *
          (∫⁻ x : Position, v x ^ ((5 : ℝ) / 2)) := by
  have hc : 0 < η * kineticCoefficient q := mul_pos hη (kineticCoefficient_pos q hq)
  have hp : Measurable (fun x : Position => density ψ x ^ ((5 : ℝ) / 3)) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_density ψ)
  have hLT : ENNReal.ofReal (kineticCoefficient q) *
      (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ := by
    rw [kineticCoefficient, Assembly.kinetic_coefficient_eq q hq]
    exact Kinetic.kinetic_lieb_thirring q hq N ψ hanti hnorm
  calc
    _ ≤ ∫⁻ x : Position, ENNReal.ofReal (η * kineticCoefficient q) *
        density ψ x ^ ((5 : ℝ) / 3) +
        ENNReal.ofReal (youngConstant * (η * kineticCoefficient q) ^ (-(3 : ℝ) / 2)) *
          v x ^ ((5 : ℝ) / 2) :=
      lintegral_mono (fun x => Assembly.young_screening _ hc (v x) (density ψ x))
    _ = ENNReal.ofReal η * (ENNReal.ofReal (kineticCoefficient q) *
        (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3))) +
        ENNReal.ofReal (youngConstant * (η * kineticCoefficient q) ^ (-(3 : ℝ) / 2)) *
          (∫⁻ x : Position, v x ^ ((5 : ℝ) / 2)) := by
      rw [lintegral_add_left (hp.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ENNReal.ofReal_mul hη.le, mul_assoc]
    _ ≤ _ := add_le_add (mul_le_mul_right hLT _) le_rfl

/-- Convert a finite extended testing integral to the real density product.
This is an arithmetic helper. -/
theorem real_density_testing_of_lintegral_le {N q : ℕ} (ψ : State N q)
    (v : Position → ℝ) (hv : Measurable v) (hn : ∀ᵐ x : Position, 0 ≤ v x)
    (A : ℝ≥0∞) (hA : A < ⊤)
    (h : (∫⁻ x : Position, ENNReal.ofReal (v x) * density ψ x) ≤ A) :
    Integrable (fun x : Position => v x * (density ψ x).toReal) ∧
      (∫ x : Position, v x * (density ψ x).toReal) ≤ A.toReal := by
  have hm := hv.ennreal_ofReal.mul (measurable_density ψ)
  have hf := h.trans_lt hA
  have heq : (fun x : Position => (ENNReal.ofReal (v x) * density ψ x).toReal) =ᵐ[volume]
      (fun x : Position => v x * (density ψ x).toReal) := by
    filter_upwards [hn] with x hx
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx]
  refine ⟨(integrable_toReal_of_lintegral_ne_top hm.aemeasurable hf.ne).congr heq, ?_⟩
  calc
    _ = ∫ x : Position, (ENNReal.ofReal (v x) * density ψ x).toReal :=
      integral_congr_ae heq.symm
    _ = (∫⁻ x : Position, ENNReal.ofReal (v x) * density ψ x).toReal :=
      integral_toReal hm.aemeasurable (ae_lt_top hm hf.ne)
    _ ≤ A.toReal := (ENNReal.toReal_le_toReal hf.ne hA.ne).mpr h

end LiebThirring.TFCore
end
