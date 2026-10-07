/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLimit.CoreComparison
public import LiebThirring.TFLimit.RegularComparison
public import LiebThirring.TFQuantum.ElectronicInfimum

/-! # Conditional molecular electronic Thomas–Fermi limit

Choose η using coefficient continuity, then δ using nuclear-core estimate, then the large-charge
threshold using regular-potential lower bound. The only remaining inputs are the uniform regular lower
bound (regular-potential lower bound with Neumann sector estimate), and the electronic upper bound (full-potential upper bound).
Coefficient continuity, finiteness, cutoff comparison, core payment and dilation are supplied
by actual ordinary-library theorems.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace LiebThirring.TFLimit

/-- The literal electronic energy expression in the limit. -/
@[expose] noncomputable def scaledElectronicEnergy (n q M : ℕ) (α : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : EReal :=
  (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
    electronicGroundStateEnergy n q M (fun k => α * z k)
      (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k)

/-- Finiteness holds even for the early zero sectors of the sequence. -/
theorem scaledElectronicEnergy_ne_top_ne_bot (q : ℕ) (hq : 1 ≤ q)
    (n M : ℕ) (α : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    scaledElectronicEnergy n q M α z R ≠ ⊤ ∧ scaledElectronicEnergy n q M α z R ≠ ⊥ := by
  have hf := electronicGroundStateEnergy_ne_top_ne_bot q hq n M
    (fun k => α * z k) (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k)
  unfold scaledElectronicEnergy
  rw [← EReal.coe_toReal hf.1 hf.2, ← EReal.coe_mul]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem tendsto_largeCharge_parameter (ν : ℝ≥0) (hν : 0 < ν)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ))) atTop atTop := by
  have hcast : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  simpa only [NNReal.coe_div, NNReal.coe_natCast] using
    hcast.atTop_div_const (show 0 < (ν : ℝ) from hν)

/-- A uniform state estimate descends to the actual finite infimum. -/
theorem scaledElectronicEnergy_lower_of_regular_bound
    (q : {q : ℕ // 1 ≤ q}) (n M : ℕ) (α : ℝ≥0) (hα : 0 < α)
    (ν : ℝ≥0) (η δ ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hlower : ∀ ψ : FormDomain n q.val, ‖ψ.val‖ = 1 →
      TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R - ε ≤
        TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ) :
    (tfEnergy (reducedKineticCoefficient q η hη1) ν z R).toReal - ε -
        TFCore.coreErrorConstant q.val z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ ≤
      (scaledElectronicEnergy n q.val M α z R).toReal := by
  have htf := tfEnergy_toReal_le_regularTFInfimum
    (reducedKineticCoefficient q η hη1) ν δ hδ z R
  have hinf : (((tfEnergy (reducedKineticCoefficient q η hη1) ν z R).toReal - ε -
      TFCore.coreErrorConstant q.val z * η ^ (-(3 : ℝ) / 2) * Real.sqrt δ : ℝ) : EReal) ≤
      scaledElectronicEnergy n q.val M α z R := by
    rw [scaledElectronicEnergy, electronicGroundStateEnergy_largeCharge_dilation α hα z R]
    apply le_iInf
    intro ψ
    apply EReal.coe_le_coe_iff.mpr
    have hreg := hlower ψ.val ψ.property
    have hcore := regularScaledQuantumEnergy_sub_core_le q.property α hα η δ hη hδ
      z R ψ.val ψ.property
    change (tfEnergy (reducedKineticCoefficient q η hη1) ν z R).toReal ≤
      TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R at htf
    linarith only [htf, hreg, hcore]
  have hf := scaledElectronicEnergy_ne_top_ne_bot q.val q.property n M α z R
  have hreal := EReal.toReal_le_toReal hinf (EReal.coe_ne_bot _) hf.1
  simpa only [EReal.toReal_coe] using hreal

/-- The electronic molecular limit follows from the two asymptotic bounds.
The two explicit inputs correspond to regular-potential lower bound with Neumann sector estimate and full-potential upper bound, respectively.
The proved coefficient-continuity theorem is consumed internally. -/
theorem tendsto_electronicGroundStateEnergy_tf_of_asymptotic_bounds
    (q : {q : ℕ // 1 ≤ q}) (M : ℕ) (_hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (_hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (_hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hlower : ∀ (η : ℝ), 0 < η → η < 1 → ∀ (δ : ℝ), 0 < δ →
      ∀ (ε : ℝ), 0 < ε → ∃ A > 0, ∀ (α : ℝ≥0), A < (α : ℝ) →
      ∀ (n : ℕ), (n : ℝ) = (α : ℝ) * (ν : ℝ) →
      ∀ (ψ : FormDomain n q.val), ‖ψ.val‖ = 1 →
        TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R - ε ≤
          TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ)
    (hupper : ∀ (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
      scaledElectronicEnergy (N j) q.val M ((N j : ℝ≥0) / ν) z R ≤
        (((tfEnergy (tfKineticConstant q) ν z R).toReal + ε : ℝ) : EReal)) :
    Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          electronicGroundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
      atTop (nhds (tfEnergy (tfKineticConstant q) ν z R)) := by
  let E := (tfEnergy (tfKineticConstant q) ν z R).toReal
  let f := fun j => scaledElectronicEnergy (N j) q.val M ((N j : ℝ≥0) / ν) z R
  have halpha := tendsto_largeCharge_parameter ν hν N hN
  have hbelow : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, E - ε < (f j).toReal := by
    intro ε hε
    have heps : 0 < ε / 3 := div_pos hε (by norm_num)
    obtain ⟨η, hη1, hη, heη⟩ := exists_kinetic_fraction_close
      q ν z R (ε / 3) heps
    obtain ⟨δ, hδ, heδ⟩ := exists_core_radius_error_lt q.val z η hη (ε / 3) heps
    obtain ⟨A, hA, hreg⟩ := hlower η hη hη1 δ hδ (ε / 3) heps
    filter_upwards [halpha.eventually (eventually_gt_atTop A)] with j hj
    let α : ℝ≥0 := (N j : ℝ≥0) / ν
    have hα : 0 < α := show 0 < (α : ℝ) from lt_trans hA hj
    have hn : (N j : ℝ) = (α : ℝ) * (ν : ℝ) := by
      dsimp only [α]
      rw [NNReal.coe_div, NNReal.coe_natCast,
        div_mul_cancel₀ _ (NNReal.coe_ne_zero.mpr hν.ne')]
    have henergy := scaledElectronicEnergy_lower_of_regular_bound q (N j) M α hα ν η δ
      (ε / 3) hη hη1 hδ z R (hreg α hj (N j) hn)
    have heη' := (abs_lt.mp heη).1
    change E - ε < (scaledElectronicEnergy (N j) q.val M α z R).toReal
    change -(ε / 3) < (tfEnergy (reducedKineticCoefficient q η hη1) ν z R).toReal - E at heη'
    linarith only [heη', heδ, henergy]
  have habove : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, (f j).toReal ≤ E + ε := by
    intro ε hε
    filter_upwards [hupper ε hε] with j hj
    have hf := scaledElectronicEnergy_ne_top_ne_bot q.val q.property (N j) M
      ((N j : ℝ≥0) / ν) z R
    have hreal := EReal.toReal_le_toReal hj hf.2 (EReal.coe_ne_top _)
    simpa only [EReal.toReal_coe] using hreal
  have hreal : Tendsto (fun j => (f j).toReal) atTop (nhds E) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hbelow (ε / 2) (half_pos hε), habove (ε / 2) (half_pos hε)] with j hlo hhi
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [hlo, hhi, hε]
  have htf := TFFunctional.tfEnergy_ne_top_ne_bot_library (tfKineticConstant q) ν z R
  have hcoe : (E : EReal) = tfEnergy (tfKineticConstant q) ν z R :=
    EReal.coe_toReal htf.1 htf.2.1
  have hfinal := EReal.tendsto_coe.mpr hreal
  rw [hcoe] at hfinal
  apply hfinal.congr'
  exact Filter.Eventually.of_forall (fun j => by
    exact EReal.coe_toReal
      (scaledElectronicEnergy_ne_top_ne_bot q.val q.property (N j) M
        ((N j : ℝ≥0) / ν) z R).1
      (scaledElectronicEnergy_ne_top_ne_bot q.val q.property (N j) M
        ((N j : ℝ≥0) / ν) z R).2)

end LiebThirring.TFLimit
end
