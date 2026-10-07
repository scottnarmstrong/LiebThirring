/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.FibreMeasurability
public import LiebThirring.Variational.FormStability

/-! # Homogeneous static stability on electronic fibres -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.ThermoStability

theorem realEnergy_extended_bound {N M q : ℕ} (C : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q)
    (h : -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖(ψ : State N q)‖ ^ 2 ≤ realEnergy z R hR ψ) :
    (∫⁻ x : Configuration N, attraction z R x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2) ≤
      kineticEnergy (ψ : State N q) +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2) +
      nuclearRepulsion z R * (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2 +
      (C : ℝ≥0∞) * (N + M : ℕ) * (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨hA, hB, hU⟩ := formDomain_coulomb_lt_top z R hR ψ
  have hmass : (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hUmass := ENNReal.mul_lt_top hU hmass
  have hCmass : (C : ℝ≥0∞) * (N + M : ℕ) * (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.natCast_lt_top _)) hmass
  have hTB := ENNReal.add_lt_top.mpr ⟨ψ.property.2, hB⟩
  have hTBU := ENNReal.add_lt_top.mpr ⟨hTB, hUmass⟩
  apply (ENNReal.toReal_le_toReal hA.ne (ENNReal.add_lt_top.mpr ⟨hTBU, hCmass⟩).ne).mp
  rw [ENNReal.toReal_add hTBU.ne hCmass.ne, ENNReal.toReal_add hTB.ne hUmass.ne,
    ENNReal.toReal_add ψ.property.2.ne hB.ne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_natCast, coe_nnnorm]
  unfold realEnergy at h
  linarith only [h]

/-- The unnormalized static constant is uniform in all nuclear configurations and counts. -/
theorem homogeneous_static_stability (q : ℕ) (hq : 1 ≤ q) (z : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (N M : ℕ) (R : Configuration M)
      (_hR : Function.Injective (fun k => particlePosition R k)) (ψ : FormDomain N q),
      (∫⁻ x : Configuration N,
        attraction (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) x *
          (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2) ≤
        kineticEnergy (ψ : State N q) +
        ((∫⁻ x : Configuration N, electronRepulsion x *
          (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2) +
          nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) *
            (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2) +
        (C : ℝ≥0∞) * (N + M : ℕ) * (‖(ψ : State N q)‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := stability_of_matter_real_unnormalized q hq (z : ℝ≥0)
  refine ⟨C, hC, ?_⟩
  intro N M R hR ψ
  have h := realEnergy_extended_bound C _ _ hR ψ
    (hbound N M (fun _ => (z : ℝ≥0)) (fun k => particlePosition R k) hR ψ (fun _ => le_rfl))
  rwa [add_assoc (kineticEnergy (ψ : State N q))] at h

end LiebThirring.ThermoStability

end
