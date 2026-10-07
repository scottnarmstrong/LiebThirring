/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactForm
public import LiebThirring.Variational.TrialVariational
public import LiebThirring.Ionization.AtomicGroundStateEnergy

/-! # Minimizing sequences for the atomic variational problem -/

public section

open MeasureTheory Filter WithLp
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- The finite atomic variational infimum admits a normalized sequence whose real energies
converge to it. -/
theorem exists_atomic_normalized_minimizing_sequence (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) :
    ∃ u : ℕ → FormDomain N q,
      (∀ n, ‖(u n : State N q)‖ = 1) ∧
      Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
        (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop
        (𝓝 (atomicGroundStateEnergy N q Z).toReal) := by
  let z : Fin 1 → ℝ≥0 := fun _ => Z
  let R : Fin 1 → Position := fun _ => 0
  let hR : Function.Injective R := fun _ _ _ => Subsingleton.elim _ _
  have hnear (n : ℕ) : ∃ v : FormDomain N q, ‖(v : State N q)‖ = 1 ∧
      realEnergy z R hR v < (atomicGroundStateEnergy N q Z).toReal + (n + 1 : ℝ)⁻¹ := by
    simpa only [atomicGroundStateEnergy, z, R, hR] using
      exists_normalized_realEnergy_lt q hq N 1 z R hR (n + 1 : ℝ)⁻¹ (by positivity)
  choose u hu hupper using hnear
  refine ⟨u, hu, ?_⟩
  have hdiff : Tendsto (fun n => realEnergy z R hR (u n) -
      (atomicGroundStateEnergy N q Z).toReal) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ => (n + 1 : ℝ)⁻¹) ?_ ?_ ?_
    · exact Eventually.of_forall fun n => sub_nonneg.mpr
        (groundStateEnergy_toReal_le_realEnergy q hq N 1 z R hR (u n) (hu n))
    · exact Eventually.of_forall fun n => sub_le_iff_le_add.mpr (by
        rw [add_comm]
        exact (hupper n).le)
    · exact tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hadd := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => (atomicGroundStateEnergy N q Z).toReal) atTop
      (𝓝 (atomicGroundStateEnergy N q Z).toReal)).add hdiff
  change Tendsto (fun n => realEnergy z R hR (u n)) atTop
    (𝓝 (atomicGroundStateEnergy N q Z).toReal)
  convert hadd using 1
  · funext n
    ring_nf
  · ring_nf

end LiebThirring

end
