/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.ExistenceLimits
public import LiebThirring.Ionization.ExistenceTight
public import LiebThirring.Variational.MinimizerEulerLagrange

/-! # Attainment for tight atomic minimizing sequences

The compactness input is a uniform particle-tail condition, supplied by the
localization bound under strict binding.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- Every tight normalized atomic minimizing sequence has a strong subsequence whose
limit attains the infimum and satisfies the full weak ground-state equation. -/
theorem exists_atomic_minimizer_subsequence_of_particle_tight (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (u : ℕ → FormDomain N q)
    (hu : ∀ n, ‖(u n : State N q)‖ = 1)
    (hE : Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop
      (𝓝 (atomicGroundStateEnergy N q Z).toReal))
    (htight : Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(u n : State N q) x‖ ^ 2) atTop) atTop (𝓝 0)) :
    ∃ v : FormDomain N q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : State N q)) atTop (𝓝 (v : State N q)) ∧
      ‖(v : State N q)‖ = 1 ∧
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) v = (atomicGroundStateEnergy N q Z).toReal ∧
      is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) v := by
  let z : Fin 1 → ℝ≥0 := fun _ => Z
  let pos : Fin 1 → Position := fun _ => 0
  let hpos : Function.Injective pos := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨K, hK⟩ := exists_formGraphNorm_bound_of_atomic_energy_tendsto Z u hu hE
  obtain ⟨v, _, φ, hφ, hweak, hstrong, _⟩ :=
    exists_formDomain_subsequence_of_particle_tight u K hK htight
  obtain ⟨ψ, hψ, hae⟩ := exists_state_subsequence_tendsto_ae hstrong
  let χ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  have hstrong' : Tendsto (fun n => (u (χ n) : State N q)) atTop (𝓝 (v : State N q)) :=
    hstrong.comp hψ.tendsto_atTop
  have hweak' : ∀ w : Sobolev.formGraph N q,
      Tendsto (fun n => inner ℂ (formDomainGraph (u (χ n))) w) atTop
        (𝓝 (inner ℂ (formDomainGraph v) w)) := fun w =>
    (hweak w).comp hψ.tendsto_atTop
  have hattr := tendsto_attraction_expectation_of_form_bounded z pos hstrong' K
    (fun n => hK (χ n))
  have hlsc := kinetic_add_repulsion_le_liminf hweak' hae K (fun n => hK (χ n))
  have hnuc : nuclearRepulsion z pos = 0 := by simp only [z, pos, nuclearRepulsion]; simp
  have hpositive : Tendsto (fun n => (kineticEnergy (u (χ n) : State N q)).toReal +
      (∫⁻ x : Configuration N,
        electronRepulsion x * (‖(u (χ n) : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal) atTop
      (𝓝 ((atomicGroundStateEnergy N q Z).toReal +
        (∫⁻ x : Configuration N, attraction z pos x *
          (‖(v : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal)) := by
    have h := (hE.comp hχ.tendsto_atTop).add hattr
    convert h using 1
    funext n
    change _ = realEnergy z pos hpos (u (χ n)) + _
    simp only [realEnergy, hnuc, ENNReal.toReal_zero, zero_mul, add_zero,
      sub_add_cancel]
  rw [hpositive.liminf_eq] at hlsc
  have hupper : realEnergy z pos hpos v ≤ (atomicGroundStateEnergy N q Z).toReal := by
    simp only [realEnergy, hnuc, ENNReal.toReal_zero, zero_mul, add_zero]
    linarith only [hlsc]
  have hvnorm : ‖(v : State N q)‖ = 1 := by
    have hn := hstrong'.norm
    simp only [hu] at hn
    exact tendsto_nhds_unique hn tendsto_const_nhds
  have hlower := groundStateEnergy_toReal_le_realEnergy q hq N 1 z pos hpos v hvnorm
  have heq : realEnergy z pos hpos v = (atomicGroundStateEnergy N q Z).toReal :=
    le_antisymm hupper hlower
  have hfin := trial_groundStateEnergy_finite q hq N 1 z pos hpos
  have hmin : groundStateEnergy N q 1 z pos hpos = (realEnergy z pos hpos v : EReal) := by
    rw [heq]
    exact (EReal.coe_toReal hfin.1 hfin.2).symm
  exact ⟨v, χ, hχ, hstrong', hvnorm, heq,
    normalized_minimizer_is_weak_ground_state z pos hpos v hvnorm hmin⟩

end LiebThirring
end
