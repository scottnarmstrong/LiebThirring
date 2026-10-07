/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingBound
public import LiebThirring.Ionization.ExistenceSequence
public import LiebThirring.Ionization.ExistenceMinimizer

/-! # Atomic minimizers and weak ground states under strict binding

The proved escaping-sector bound supplies tightness for every normalized
minimizing sequence; compact extraction then attains the original infimum.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- Strict binding prevents loss of mass in every normalized minimizing sequence. -/
theorem atomic_particle_tight_of_binding (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (Z : ℝ≥0)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z)
    (u : ℕ → FormDomain N q) (hu : ∀ n, ‖(u n : State N q)‖ = 1)
    (hE : Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop
      (𝓝 (atomicGroundStateEnergy N q Z).toReal)) :
    Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(u n : State N q) x‖ ^ 2) atTop) atTop (𝓝 0) :=
  atomic_particle_tight_of_localization_bounds Z u hu
    (atomicGroundStateEnergy_toReal_lt_of_lt q hq N Z hbind) hE
    (fun _ hR n => atomic_realEnergy_ge_inside_mass q hq N Z hR (u n) (hu n))

/-- Every normalized minimizing sequence under strict atomic binding has a strong
subsequence converging to a normalized minimizer and a weak ground state. -/
theorem exists_atomic_minimizer_subsequence_of_binding (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z)
    (u : ℕ → FormDomain N q) (hu : ∀ n, ‖(u n : State N q)‖ = 1)
    (hE : Tendsto (fun n => realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) (u n)) atTop
      (𝓝 (atomicGroundStateEnergy N q Z).toReal)) :
    ∃ v : FormDomain N q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (u (φ n) : State N q)) atTop (𝓝 (v : State N q)) ∧
      ‖(v : State N q)‖ = 1 ∧
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) v = (atomicGroundStateEnergy N q Z).toReal ∧
      is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) v :=
  exists_atomic_minimizer_subsequence_of_particle_tight q hq N Z u hu hE
    (atomic_particle_tight_of_binding q hq N Z hbind u hu hE)

/-- Strict atomic binding yields a weak ground state on the original form domain. -/
theorem exists_atomic_weak_ground_state_of_binding (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    ∃ ψ : FormDomain N q,
      is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
        (fun _ _ _ => Subsingleton.elim _ _) ψ := by
  obtain ⟨u, hu, hE⟩ := exists_atomic_normalized_minimizing_sequence q hq N Z
  obtain ⟨v, _, _, _, _, _, hweak⟩ :=
    exists_atomic_minimizer_subsequence_of_binding q hq N Z hbind u hu hE
  exact ⟨v, hweak⟩

end LiebThirring
end
