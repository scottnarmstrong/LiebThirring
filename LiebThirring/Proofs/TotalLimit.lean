/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy
public import LiebThirring.ThomasFermi.Energy
public import LiebThirring.ThomasFermi.KineticConstant
import LiebThirring.TFLimit.FinalLimits
import LiebThirring.TFProduct.SpectralData

/-!
# Total molecular Thomas–Fermi limit

The electronic molecular limit and exact homogeneity of nuclear repulsion give
the total-energy limit with the nuclear constant on both sides.
Source: Lieb–Simon (1977), Theorem III.1, equation (45); Lieb (1981), Theorem 5.1.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem tendsto_groundStateEnergy_tf (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hRN : ∀ j, Function.Injective
      (fun k => ((((N j : ℝ≥0) / ν : ℝ≥0) : ℝ) ^ (-(1 : ℝ) / 3)) • R k)) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          groundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k) (hRN j))
      Filter.atTop
      (nhds (tfEnergy (tfKineticConstant q) ν z R +
        ((nuclearRepulsion z R).toReal : EReal))) :=
  LiebThirring.TFLimit.tendsto_groundStateEnergy_tf_of_neumann_spectral_data
    q M hM ν hν z hz R hR N hN hRN
    (fun _ ℓ b => LiebThirring.TFProduct.neumannProductSpectralData ℓ b)

end LiebThirring.Proofs

end
