/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.ElectronicGroundStateEnergy
public import LiebThirring.ThomasFermi.Energy
public import LiebThirring.ThomasFermi.KineticConstant
public import Mathlib.Topology.Instances.EReal.Lemmas
import LiebThirring.Proofs.MolecularLimit

/-! # Molecular Thomas–Fermi electronic energy limit -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Fixed molecular data and fixed spin; no eigenfunction or minimizer hypothesis. -/
theorem tendsto_electronicGroundStateEnergy_tf (q : {q : ℕ // 1 ≤ q})
    (M : ℕ) (hM : 1 ≤ M) (ν : ℝ≥0) (hν : 0 < ν)
    (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (N : ℕ → ℕ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun j =>
        let α : ℝ≥0 := (N j : ℝ≥0) / ν
        (((α : ℝ) ^ (-(7 : ℝ) / 3) : ℝ) : EReal) *
          electronicGroundStateEnergy (N j) q.val M
            (fun k => α * z k)
            (fun k => ((α : ℝ) ^ (-(1 : ℝ) / 3)) • R k))
      Filter.atTop (nhds (tfEnergy (tfKineticConstant q) ν z R)) :=
  by exact LiebThirring.Proofs.tendsto_electronicGroundStateEnergy_tf q M hM ν hν z hz R hR N hN

end LiebThirring

end
