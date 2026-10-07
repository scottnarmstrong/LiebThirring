/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSRamp

/-! # Mass and tail estimates for the radial IMS sectors

The IMS partition gives exact mass identities and tail estimates.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring
open Sobolev

/-- The state localized to an inside-particle subset by the literal radial partition. -/
@[expose] noncomputable def imsLocalizedState {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin N)) (u : State N q) : State N q :=
  lipschitzBoundedSMul (imsSectorWeight (imsChi R) (imsEta R) S) 1
    (norm_imsSectorWeight_le_one R S) (lipschitzWith_imsSectorWeight hR S) u

/-- Mass of the all-inside sector. -/
@[expose] noncomputable def imsInsideMass {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) : ℝ := ‖imsLocalizedState hR Finset.univ u‖ ^ 2

/-- The localized state has the expected multiplication representative. -/
theorem imsLocalizedState_coeFn {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin N)) (u : State N q) :
    imsLocalizedState hR S u =ᵐ[volume]
      fun x => (imsSectorWeight (imsChi R) (imsEta R) S x : ℂ) • u x :=
  lipschitzBoundedSMul_coeFn _ _ _ _ _

/-- The radial IMS partition preserves total mass. -/
theorem sum_imsLocalizedState_norm_sq {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) :
    (∑ S : Finset (Fin N), ‖imsLocalizedState hR S u‖ ^ 2) = ‖u‖ ^ 2 :=
  sum_norm_lipschitz_partition_sq u _ (fun _ => 1)
    (fun S => norm_imsSectorWeight_le_one R S) _
    (fun S => lipschitzWith_imsSectorWeight hR S) (sum_all_imsSectorWeight_sq R)

/-- All-inside mass is nonnegative. -/
theorem imsInsideMass_nonneg {N q : ℕ} {R : ℝ} (hR : 0 < R) (u : State N q) :
    0 ≤ imsInsideMass hR u := sq_nonneg _

/-- A particle beyond twice the localization radius makes the all-inside weight vanish. -/
theorem imsSectorWeight_univ_eq_zero_of_particle_tail {N : ℕ} {R : ℝ}
    (hR : 0 < R) {x : Configuration N}
    (hx : ∃ i : Fin N, 2 * R < ‖particlePosition x i‖) :
    imsSectorWeight (imsChi R) (imsEta R) Finset.univ x = 0 := by
  obtain ⟨i, hi⟩ := hx
  have hz := imsChi_eq_zero_of_two_mul_le_norm hR hi.le
  simp only [imsSectorWeight, Finset.sdiff_self, Finset.prod_empty, mul_one]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- Literal particle-tail sets are measurable. -/
theorem measurableSet_particle_tail (N : ℕ) (R : ℝ) :
    MeasurableSet {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖} := by
  have h : ∀ i : Fin N, MeasurableSet {x : Configuration N | R < ‖particlePosition x i‖} :=
    fun i => measurableSet_lt measurable_const
      (lipschitzWith_particlePosition i).continuous.measurable.norm
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion h

/-- The all-inside cutoff controls the full union of particle tails, with no spin factor. -/
theorem particle_tail_le_one_sub_inside_mass {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) (hu : ‖u‖ = 1) :
    (∫ x in {x : Configuration N | ∃ i : Fin N, 2 * R < ‖particlePosition x i‖},
      ‖u x‖ ^ 2) ≤ 1 - imsInsideMass hR u := by
  let b : Set (Configuration N) := {x | ∃ i : Fin N, 2 * R < ‖particlePosition x i‖}
  have hb : MeasurableSet b := measurableSet_particle_tail N (2 * R)
  have hrep := imsLocalizedState_coeFn hR Finset.univ u
  have hzero : (∫ x in b, ‖imsLocalizedState hR Finset.univ u x‖ ^ 2) = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards [hrep] with x hx
    intro hxb
    rw [hx, imsSectorWeight_univ_eq_zero_of_particle_tail hR hxb,
      Complex.ofReal_zero, zero_smul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hins : imsInsideMass hR u ≤ ∫ x in bᶜ, ‖u x‖ ^ 2 := by
    have htotal := integral_add_compl hb
      (integrable_state_norm_sq (imsLocalizedState hR Finset.univ u))
    rw [hzero, zero_add, integral_state_norm_sq] at htotal
    rw [imsInsideMass, ← htotal]
    apply integral_mono_ae (integrable_state_norm_sq _).integrableOn
      (integrable_state_norm_sq u).integrableOn
    filter_upwards [ae_restrict_of_ae hrep] with x hx
    rw [hx, norm_smul]
    apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ 2
    calc
      _ ≤ 1 * ‖u x‖ := mul_le_mul_of_nonneg_right
        (by simpa only [Complex.norm_real] using norm_imsSectorWeight_le_one R Finset.univ x)
        (norm_nonneg _)
      _ = _ := one_mul _
  have hmass := integral_add_compl hb (integrable_state_norm_sq u)
  rw [integral_state_norm_sq, hu, one_pow] at hmass
  linarith only [hins, hmass]

end LiebThirring
end
