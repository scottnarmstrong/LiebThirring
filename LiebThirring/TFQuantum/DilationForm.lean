/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationKinetic
public import LiebThirring.TFQuantum.DilationCoulomb
public import LiebThirring.TFQuantum.ElectronicForm
/-! # Dilation of the form domain and its literal infimum

Spatial dilation is a bijection of the finite-kinetic fermionic form domain
and its normalized subtype. Changing competitors by this bijection gives
equality of the literal electronic infimum with the dilated Hamiltonian.
direct proof calculation.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

@[expose] noncomputable def formDomainDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r) :
    FormDomain N q ≃ FormDomain N q where
  toFun ψ := ⟨stateDilationEquiv r hr ψ.val,
    antisymmetric_stateDilationEquiv r hr ψ.val ψ.property.1, by
      rw [kineticEnergy_stateDilationEquiv]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ψ.property.2⟩
  invFun ψ := ⟨stateDilationEquiv r⁻¹ (inv_pos.mpr hr) ψ.val,
    antisymmetric_stateDilationEquiv r⁻¹ (inv_pos.mpr hr) ψ.val ψ.property.1, by
      rw [kineticEnergy_stateDilationEquiv]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ψ.property.2⟩
  left_inv ψ := Subtype.ext (stateDilationEquiv_inv_apply r hr ψ.val)
  right_inv ψ := Subtype.ext (stateDilationEquiv_apply_inv r hr ψ.val)

@[expose] noncomputable def electronicTrialDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r) :
    ElectronicTrial N q ≃ ElectronicTrial N q where
  toFun ψ := ⟨formDomainDilationEquiv r hr ψ.val, by
    change ‖stateDilationEquiv r hr ψ.val.val‖ = 1
    rw [stateDilationEquiv_norm, ψ.property]⟩
  invFun ψ := ⟨(formDomainDilationEquiv r hr).symm ψ.val, by
    change ‖stateDilationEquiv r⁻¹ (inv_pos.mpr hr) ψ.val.val‖ = 1
    rw [stateDilationEquiv_norm, ψ.property]⟩
  left_inv ψ := Subtype.ext ((formDomainDilationEquiv r hr).symm_apply_apply ψ.val)
  right_inv ψ := Subtype.ext ((formDomainDilationEquiv r hr).apply_symm_apply ψ.val)

@[simp] theorem electronicTrialDilationEquiv_val {N q : ℕ} (r : ℝ) (hr : 0 < r)
    (ψ : ElectronicTrial N q) : (electronicTrialDilationEquiv r hr ψ).val =
      formDomainDilationEquiv r hr ψ.val := rfl

theorem electronicEnergy_formDomainDilationEquiv {N q M : ℕ} (r : ℝ) (hr : 0 < r)
    (β : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q) :
    electronicEnergy (fun k => β * z k) (fun k => r⁻¹ • R k) (formDomainDilationEquiv r hr ψ) =
      r^2 * (kineticEnergy ψ.val).toReal + r *
        (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ.val x‖₊ : ℝ≥0∞)^2).toReal -
      (β : ℝ) * r *
        (∫⁻ x : Configuration N, attraction z R x * (‖ψ.val x‖₊ : ℝ≥0∞)^2).toReal := by
  unfold electronicEnergy
  have hval : (formDomainDilationEquiv r hr ψ).val = stateDilationEquiv r hr ψ.val := rfl
  simp only [hval]
  rw [kineticEnergy_stateDilationEquiv, repulsion_stateDilationEquiv,
    attraction_stateDilationEquiv]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sq_nonneg r), ENNReal.toReal_ofReal hr.le]

namespace Dilation
@[expose] noncomputable def erealMulOrderIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal :=
  (OrderIso.mulLeft₀ c hc).withTopCongr.withBotCongr

theorem erealMulOrderIso_apply (c : ℝ) (hc : 0 < c) (x : EReal) :
    erealMulOrderIso c hc x = (c : EReal) * x := by
  induction x using EReal.rec with
  | bot => exact (EReal.coe_mul_bot_of_pos hc).symm
  | top => exact (EReal.coe_mul_top_of_pos hc).symm
  | coe x => exact EReal.coe_mul c x

theorem ereal_mul_iInf {ι : Sort*} (c : ℝ) (hc : 0 < c) (f : ι → EReal) :
    (c : EReal) * (⨅ i, f i) = ⨅ i, (c : EReal) * f i := by
  simpa only [erealMulOrderIso_apply] using (erealMulOrderIso c hc).map_iInf f
end Dilation
end LiebThirring
end
