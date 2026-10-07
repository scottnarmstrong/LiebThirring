/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationForm
/-! # Exact large-charge normalization of electronic energy

At scale r = α^(1/3), the unitary has amplitude α^(N/2). Dividing the
physical electronic energy by α^(7/3) gives the literal coefficients
α^(-5/3) T + α^(-2) B - α^(-1) A on the original form carrier. The
competitor bijection proves equality of infima, and the nuclear constant
scales by α^(7/3). Proof: large-charge dilation, direct proof calculation;
Lieb–Simon (1977) III.1 and III.5; NFA section 8.4, p. 157.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

@[expose] noncomputable def largeChargeScale (α : ℝ≥0) : ℝ := (α : ℝ)^((1 : ℝ)/3)

theorem largeChargeScale_pos (α : ℝ≥0) (hα : 0 < α) : 0 < largeChargeScale α :=
  Real.rpow_pos_of_pos (show 0 < (α : ℝ) from hα) _

theorem largeChargeScale_inv (α : ℝ≥0) :
    (largeChargeScale α)⁻¹ = (α : ℝ)^(-(1 : ℝ)/3) := by
  rw [neg_div, Real.rpow_neg α.coe_nonneg]
  rfl

theorem largeChargeScale_sq (α : ℝ≥0) :
    (largeChargeScale α)^2 = (α : ℝ)^((2 : ℝ)/3) := by
  rw [largeChargeScale, ← Real.rpow_mul_natCast α.coe_nonneg]
  congr 1
  norm_num

namespace Dilation

theorem largeCharge_kinetic_coeff (α : ℝ≥0) (hα : 0 < α) :
    (α : ℝ)^(-(7 : ℝ)/3) * (largeChargeScale α)^2 = (α : ℝ)^(-(5 : ℝ)/3) := by
  rw [largeChargeScale_sq, ← Real.rpow_add (show 0 < (α : ℝ) from hα)]
  congr 1
  norm_num

theorem largeCharge_repulsion_coeff (α : ℝ≥0) (hα : 0 < α) :
    (α : ℝ)^(-(7 : ℝ)/3) * largeChargeScale α = (α : ℝ)^(-(2 : ℝ)) := by
  rw [largeChargeScale, ← Real.rpow_add (show 0 < (α : ℝ) from hα)]
  congr 1
  norm_num

theorem largeCharge_attraction_coeff (α : ℝ≥0) (hα : 0 < α) :
    (α : ℝ)^(-(7 : ℝ)/3) * (α : ℝ) * largeChargeScale α = (α : ℝ)^(-(1 : ℝ)) := by
  have hp : 0 < (α : ℝ) := hα
  calc
    _ = (α : ℝ)^(-(7 : ℝ)/3) * (α : ℝ)^(1 : ℝ) * (α : ℝ)^((1 : ℝ)/3) := by
      rw [Real.rpow_one]
      rfl
    _ = (α : ℝ)^(-(7 : ℝ)/3 + 1 + (1 : ℝ)/3) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]
    _ = _ := by congr 1; norm_num

theorem largeCharge_nuclear_coeff (α : ℝ≥0) (hα : 0 < α) :
    (α : ℝ)^2 * largeChargeScale α = (α : ℝ)^((7 : ℝ)/3) := by
  rw [largeChargeScale, ← Real.rpow_natCast, ← Real.rpow_add (show 0 < (α : ℝ) from hα)]
  congr 1
  norm_num

end Dilation

/-- The literal normalized large-charge Hamiltonian on the form carrier. -/
@[expose] noncomputable def dilatedElectronicEnergy {N q M : ℕ} (α : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) : ℝ :=
  (α : ℝ)^(-(5 : ℝ)/3) * (kineticEnergy ψ.val).toReal +
    (α : ℝ)^(-(2 : ℝ)) *
      (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ.val x‖₊ : ℝ≥0∞)^2).toReal -
    (α : ℝ)^(-(1 : ℝ)) *
      (∫⁻ x : Configuration N, attraction z R x * (‖ψ.val x‖₊ : ℝ≥0∞)^2).toReal

theorem electronicEnergy_largeCharge_dilation {N q M : ℕ} (α : ℝ≥0) (hα : 0 < α)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) :
    (α : ℝ)^(-(7 : ℝ)/3) * electronicEnergy (fun k => α * z k)
      (fun k => ((α : ℝ)^(-(1 : ℝ)/3)) • R k)
      (formDomainDilationEquiv (largeChargeScale α) (largeChargeScale_pos α hα) ψ) =
    dilatedElectronicEnergy α z R ψ := by
  rw [← largeChargeScale_inv, electronicEnergy_formDomainDilationEquiv]
  simp only [dilatedElectronicEnergy, mul_add, mul_sub, ← mul_assoc,
    Dilation.largeCharge_kinetic_coeff α hα, Dilation.largeCharge_repulsion_coeff α hα,
    Dilation.largeCharge_attraction_coeff α hα]

theorem electronicGroundStateEnergy_largeCharge_dilation {N q M : ℕ} (α : ℝ≥0) (hα : 0 < α)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (((α : ℝ)^(-(7 : ℝ)/3) : ℝ) : EReal) *
      electronicGroundStateEnergy N q M (fun k => α * z k)
        (fun k => ((α : ℝ)^(-(1 : ℝ)/3)) • R k) =
      ⨅ ψ : ElectronicTrial N q, (dilatedElectronicEnergy α z R ψ.val : EReal) := by
  rw [electronicGroundStateEnergy_eq_iInf_electronicEnergy,
    ← (electronicTrialDilationEquiv (largeChargeScale α) (largeChargeScale_pos α hα)).surjective.iInf_comp,
    Dilation.ereal_mul_iInf _ (Real.rpow_pos_of_pos (show 0 < (α : ℝ) from hα) _)]
  apply iInf_congr
  intro ψ
  rw [← EReal.coe_mul, electronicTrialDilationEquiv_val,
    electronicEnergy_largeCharge_dilation α hα z R ψ.val]

theorem nuclearRepulsion_largeCharge {M : ℕ} (α : ℝ≥0) (hα : 0 < α)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    nuclearRepulsion (fun k => α * z k) (fun k => ((α : ℝ)^(-(1 : ℝ)/3)) • R k) =
      ENNReal.ofReal ((α : ℝ)^((7 : ℝ)/3)) * nuclearRepulsion z R := by
  have h := Dilation.nuclearRepulsion_dilation (largeChargeScale α)
    (largeChargeScale_pos α hα) α z R
  have hc : (α : ℝ≥0∞)^2 * ENNReal.ofReal (largeChargeScale α) =
      ENNReal.ofReal ((α : ℝ)^((7 : ℝ)/3)) := by
    rw [← Dilation.largeCharge_nuclear_coeff α hα,
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
  rw [largeChargeScale_inv, hc] at h
  exact h

theorem nuclearRepulsion_largeCharge_normalized {M : ℕ} (α : ℝ≥0) (hα : 0 < α)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    ENNReal.ofReal ((α : ℝ)^(-(7 : ℝ)/3)) *
      nuclearRepulsion (fun k => α * z k) (fun k => ((α : ℝ)^(-(1 : ℝ)/3)) • R k) =
    nuclearRepulsion z R := by
  rw [nuclearRepulsion_largeCharge α hα, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg α.coe_nonneg _),
    ← Real.rpow_add (show 0 < (α : ℝ) from hα)]
  norm_num

theorem nuclearRepulsion_largeCharge_normalized_toReal {M : ℕ} (α : ℝ≥0) (hα : 0 < α)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    (α : ℝ)^(-(7 : ℝ)/3) *
      (nuclearRepulsion (fun k => α * z k)
        (fun k => ((α : ℝ)^(-(1 : ℝ)/3)) • R k)).toReal = (nuclearRepulsion z R).toReal := by
  have h := congrArg ENNReal.toReal (nuclearRepulsion_largeCharge_normalized α hα z R)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg α.coe_nonneg _)] using h

end LiebThirring
end
