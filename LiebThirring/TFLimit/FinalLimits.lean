/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLimit.TotalEnergy
public import LiebThirring.TFSectors.SpectralInput
import LiebThirring.TFSectors.LowerRegular
import LiebThirring.TFFilled.FullUpperInputs

/-! # The molecular Thomas–Fermi limits from Neumann product spectral data

The conclusions are the electronic and total Thomas--Fermi energy limits.
The proved lower and unconditional upper estimates supply the two inputs
of the limit assembly. The exact spectral-data family of LowerRegular remains an explicit hypothesis.

Lieb–Simon (1977) III.1/III.5, pp. 57 and 72--75;
The total conclusion includes the nuclear constant.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFLimit

/-- The literal electronic limit, conditional only on LowerRegular's
Neumann product spectral-data family. -/
theorem tendsto_electronicGroundStateEnergy_tf_of_neumann_spectral_data (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (spectral : ∀ (N : ℕ) (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex),
      TFSectors.NeumannProductSpectralData N q.val ℓ b) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          electronicGroundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
      Filter.atTop (nhds (tfEnergy (tfKineticConstant q) ν z R)) := by
  exact tendsto_electronicGroundStateEnergy_tf_of_asymptotic_bounds
    q M hM ν hν z hz R hR N hN
    (TFSectors.regularScaledQuantumEnergy_eventually_ge_reduced_kinetic_of_neumann_spectral_data
      q ν z R spectral)
    (TFFilled.scaledElectronicEnergy_eventually_le q ν hν z R N hN)

/-- The literal total limit, conditional only on LowerRegular's
Neumann product spectral-data family. -/
theorem tendsto_groundStateEnergy_tf_of_neumann_spectral_data (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hRN : ∀ j, Function.Injective
      (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
    (spectral : ∀ (N : ℕ) (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex),
      TFSectors.NeumannProductSpectralData N q.val ℓ b) :
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
  exact tendsto_groundStateEnergy_tf_of_asymptotic_bounds
    q M hM ν hν z hz R hR N hN hRN
    (TFSectors.regularScaledQuantumEnergy_eventually_ge_reduced_kinetic_of_neumann_spectral_data
      q ν z R spectral)
    (TFFilled.scaledElectronicEnergy_eventually_le q ν hν z R N hN)

end LiebThirring.TFLimit
end
