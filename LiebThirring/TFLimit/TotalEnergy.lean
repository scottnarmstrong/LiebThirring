/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLimit.ElectronicLimit
public import LiebThirring.TFQuantum.ElectronicTotal

/-! # Assembly of the Thomas--Fermi total-energy limit

This module internally derives the electronic Thomas--Fermi limit from the
regular-potential and Neumann-sector lower estimates and the full-potential upper estimate, then uses exact nuclear scaling and the
proved electronic/total bridge. It is an identity for the total variational energy.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFLimit

private theorem eventually_largeChargeScale_pos (ν : ℝ≥0) (hν : 0 < ν)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop) :
    ∀ᶠ j in Filter.atTop, 0 < (N j : ℝ≥0) / ν := by
  filter_upwards [hN.eventually_ge_atTop 1] with j hj
  exact div_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hj)) hν

/-- Conditional assembly of the total-energy conclusion from one
literal electronic Thomas--Fermi limit. -/
private theorem tendsto_groundStateEnergy_tf_of_electronic_limit (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hRN : ∀ j, Function.Injective
      (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
    (hElectronic :
      Filter.Tendsto
        (fun j =>
          let α : ℝ≥0 := (N j : ℝ≥0) / ν
          (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
            electronicGroundStateEnergy (N j) q.val M
              (fun k => α * z k)
              (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
        Filter.atTop (nhds (tfEnergy (tfKineticConstant q) ν z R))) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          groundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) (hRN j))
      Filter.atTop
      (nhds (tfEnergy (tfKineticConstant q) ν z R +
        ((nuclearRepulsion z R).toReal : EReal))) := by
  have _hdata : 1 ≤ M ∧ ∀ k, 0 < z k := ⟨hM, hz⟩
  have _hnuclearFinite : nuclearRepulsion z R < ⊤ :=
    LiebThirring.Assembly.nuclearRepulsion_lt_top z R hR
  have htf := TFFunctional.tfEnergy_ne_top_ne_bot_library
    (tfKineticConstant q) ν z R
  have hadd : Filter.Tendsto
      (fun j =>
        (let α : ℝ≥0 := (N j : ℝ≥0) / ν;
          (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
              electronicGroundStateEnergy (N j) q.val M
              (fun k => α * z k)
              (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) +
          ((nuclearRepulsion z R).toReal : EReal)))
      Filter.atTop
      (nhds (tfEnergy (tfKineticConstant q) ν z R +
        ((nuclearRepulsion z R).toReal : EReal))) := by
    exact (EReal.continuousAt_add (Or.inl htf.1) (Or.inl htf.2.1)).tendsto.comp
      (hElectronic.prodMk_nhds tendsto_const_nhds)
  apply hadd.congr'
  filter_upwards [eventually_largeChargeScale_pos ν hν N hN] with j hα
  dsimp only
  rw [groundStateEnergy_eq_electronic_add_nuclear q.val q.property]
  rw [EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) (EReal.coe_ne_top _)]
  congr 1
  rw [← EReal.coe_mul]
  congr 1
  exact (nuclearRepulsion_largeCharge_normalized_toReal
    ((N j : ℝ≥0) / ν) hα z R).symm

/-- Conditional total limit with exactly the two remaining regular-potential lower bound/Neumann sector estimate and full-potential upper bound
inputs. The electronic limit, coefficient continuity and dilation bridges are internal. -/
theorem tendsto_groundStateEnergy_tf_of_asymptotic_bounds
    (q : {q : ℕ // 1 ≤ q}) (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hRN : ∀ j, Function.Injective
      (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
    (hlower : ∀ (η : ℝ), 0 < η → η < 1 → ∀ (δ : ℝ), 0 < δ →
      ∀ (ε : ℝ), 0 < ε → ∃ A > 0, ∀ (α : ℝ≥0), A < (α : ℝ) →
      ∀ (n : ℕ), (n : ℝ) = (α : ℝ) * (ν : ℝ) →
      ∀ (ψ : FormDomain n q.val), ‖ψ.val‖ = 1 →
        TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R - ε ≤
          TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ)
    (hupper : ∀ (ε : ℝ), 0 < ε → ∀ᶠ j in Filter.atTop,
      scaledElectronicEnergy (N j) q.val M ((N j : ℝ≥0) / ν) z R ≤
        (((tfEnergy (tfKineticConstant q) ν z R).toReal + ε : ℝ) : EReal)) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          groundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) (hRN j))
      Filter.atTop
      (nhds (tfEnergy (tfKineticConstant q) ν z R +
        ((nuclearRepulsion z R).toReal : EReal))) := by
  apply tendsto_groundStateEnergy_tf_of_electronic_limit
    q M hM ν hν z hz R hR N hN hRN
  exact tendsto_electronicGroundStateEnergy_tf_of_asymptotic_bounds
    q M hM ν hν z hz R hR N hN hlower hupper

end LiebThirring.TFLimit

end
