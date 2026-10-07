/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.CompactMass

/-! # Compact coordinate boxes for many-particle configurations

Coordinate boxes provide compact spatial sets whose complements are controlled by the union of
the one-particle radial tails.
-/

public section

open MeasureTheory Set WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The closed box on which every scalar configuration coordinate has absolute value at most `R`. -/
@[expose] def configurationBox (N : ℕ) (R : ℝ) : Set (Configuration N) :=
  {x | ∀ a : Fin N × Fin 3, |x a| ≤ R}

/-- A finite-dimensional coordinate box is compact. -/
theorem configurationBox_isCompact (N : ℕ) (R : ℝ) :
    IsCompact (configurationBox N R) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin N × Fin 3 => ℝ)).toHomeomorph
  have hpi : IsCompact (Set.univ.pi fun _ : Fin N × Fin 3 => Set.Icc (-R) R) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have heq : configurationBox N R =
      e ⁻¹' (Set.univ.pi fun _ : Fin N × Fin 3 => Set.Icc (-R) R) := by
    ext x
    simp only [configurationBox, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies,
      mem_Icc]
    constructor
    · intro hx a
      exact (abs_le.mp (hx a))
    · intro hx a
      exact abs_le.mpr (hx a)
  rw [heq]
  exact (e.isCompact_preimage).mpr hpi

/-- Coordinate boxes are measurable. -/
theorem configurationBox_measurableSet (N : ℕ) (R : ℝ) :
    MeasurableSet (configurationBox N R) :=
  (configurationBox_isCompact N R).measurableSet

/-- Coordinate boxes have finite volume. -/
theorem configurationBox_volume_lt_top (N : ℕ) (R : ℝ) :
    volume (configurationBox N R) < ⊤ :=
  (configurationBox_isCompact N R).measure_lt_top

/-- Outside the coordinate box, at least one particle has radius greater than `R`. -/
theorem configurationBox_compl_subset_particle_tail (N : ℕ) (R : ℝ) :
    (configurationBox N R)ᶜ ⊆
      {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖} := by
  intro x hx
  have hx' : ¬ ∀ a : Fin N × Fin 3, |x a| ≤ R := hx
  push Not at hx'
  obtain ⟨⟨i, a⟩, hia⟩ := hx'
  refine ⟨i, hia.trans_le ?_⟩
  simpa only [particlePosition, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (particlePosition x i) a)

/-- Mass outside a coordinate box is bounded by the literal union of particle radial tails. -/
theorem integral_compl_configurationBox_norm_sq_le_particle_tail {N q : ℕ}
    (R : ℝ) (u : State N q) :
    (∫ x in (configurationBox N R)ᶜ, ‖u x‖ ^ 2) ≤
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖u x‖ ^ 2 := by
  apply setIntegral_mono_set (integrable_state_norm_sq u).integrableOn
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖u x‖)
  exact (configurationBox_compl_subset_particle_tail N R).eventuallySubset

end LiebThirring

end
