/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.ScalingFunctional
public import LiebThirring.ThomasFermi.Energy

/-! # Exact scaling of Thomas--Fermi energy -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

private noncomputable def erealMulPosOrderIso (c : ℝ) (hc : 0 < c) : EReal ≃o EReal where
  toFun x := (c : EReal) * x
  invFun x := ((c⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    dsimp
    rw [← mul_assoc, ← EReal.coe_mul]
    simp [hc.ne']
  right_inv x := by
    dsimp
    rw [← mul_assoc, ← EReal.coe_mul]
    simp [hc.ne']
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      change (c : EReal) * x ≤ (c : EReal) * y at h
      have hm := mul_le_mul_of_nonneg_left h
        (EReal.coe_nonneg.mpr (inv_nonneg.mpr hc.le) : (0 : EReal) ≤ (c⁻¹ : ℝ))
      simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one,
        one_mul] using hm
    · exact fun h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le)

/-- Exact TF energy scaling, parameterized by the inverse length scale. -/
theorem tfEnergy_dilation {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (β : ℝ) (hβ : 0 < β) :
    tfEnergy a ((Real.toNNReal β) ^ 3 * ν)
        (fun k => (Real.toNNReal β) ^ 3 * z k) (fun k => β⁻¹ • R k) =
      (β ^ 7 : EReal) * tfEnergy a ν z R := by
  unfold tfEnergy
  simp only [NNReal.coe_mul, NNReal.coe_pow]
  rw [Real.coe_toNNReal β hβ.le]
  rw [← (tfDensityDilationMassEquiv β hβ (ν : ℝ)).iInf_comp]
  have hfun : ∀ ρ : {ρ : TFDensity // tfMass ρ = (ν : ℝ)},
      (tfFunctional a (fun k => (Real.toNNReal β) ^ 3 * z k)
        (fun k => β⁻¹ • R k)
        ((tfDensityDilationMassEquiv β hβ (ν : ℝ)) ρ).val : EReal) =
      (β ^ 7 : EReal) * (tfFunctional a z R ρ.val : EReal) := by
    intro ρ
    simp only [tfDensityDilationMassEquiv, Equiv.subtypeEquiv,
      tfDensityDilationEquiv]
    change (tfFunctional a (fun k => (Real.toNNReal β) ^ 3 * z k)
      (fun k => β⁻¹ • R k)
      (tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ.val) : EReal) = _
    rw [tfFunctional_tfDensityDilation, EReal.coe_mul, EReal.coe_pow]
  simp_rw [hfun]
  exact ((erealMulPosOrderIso (β ^ 7) (pow_pos hβ 7)).map_iInf
    (fun ρ : {ρ : TFDensity // tfMass ρ = (ν : ℝ)} =>
      (tfFunctional a z R ρ.val : EReal))).symm

end LiebThirring

end
