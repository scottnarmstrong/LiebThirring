/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedRadial
public import LiebThirring.Variational.SpectatorMultiplier
public import LiebThirring.Variational.FormAlgebra

/-! # The admissible symmetric sum of bounded ionization weights

Implements the sum test in the cutoff pair estimate. Individual selected-coordinate
products are states with finite kinetic energy.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
open Sobolev

/-- The bounded radial weight of a selected electron. -/
@[expose] noncomputable def ionizationParticleWeight {N : ℕ} (ε : ℝ) (i : Fin N)
    (X : Configuration N) : ℝ := ionizationWeight ε ‖particlePosition X i‖

/-- The permutation-invariant sum used in the actual weak equation. -/
@[expose] noncomputable def ionizationSumWeight {N : ℕ} (ε : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ionizationParticleWeight ε i X

theorem lipschitzWith_ionizationParticleWeight {N : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (i : Fin N) : LipschitzWith 1 (ionizationParticleWeight ε i) :=
  lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε)

theorem norm_ionizationParticleWeight_le {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i : Fin N) (X : Configuration N) : ‖ionizationParticleWeight ε i X‖ ≤ ε⁻¹ := by
  unfold ionizationParticleWeight
  rw [Real.norm_eq_abs, abs_of_nonneg (ionizationWeight_nonneg hε.le (norm_nonneg _))]
  exact ionizationWeight_le_inv hε (norm_nonneg _)

theorem norm_ionizationSumWeight_le {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (X : Configuration N) : ‖ionizationSumWeight ε X‖ ≤ (N : ℝ) * ε⁻¹ := by
  calc
    _ ≤ ∑ i : Fin N, ‖ionizationParticleWeight ε i X‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ε⁻¹ := Finset.sum_le_sum (fun i _ =>
      norm_ionizationParticleWeight_le ε hε i X)
    _ = _ := by simp

theorem lipschitzWith_ionizationSumWeight {N : ℕ} (ε : ℝ) (hε : 0 ≤ ε) :
    LipschitzWith (N : ℝ≥0) (ionizationSumWeight (N := N) ε) := by
  apply LipschitzWith.of_le_add_mul
  intro X Y
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    (lipschitzWith_ionizationParticleWeight ε hε i).le_add_mul X Y)
  simpa only [ionizationSumWeight, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, NNReal.coe_one, one_mul, NNReal.coe_natCast] using h

theorem ionizationSumWeight_permutePositions {N : ℕ} (ε : ℝ)
    (σ : Equiv.Perm (Fin N)) (X : Configuration N) :
    ionizationSumWeight ε (permutePositions σ X) = ionizationSumWeight ε X := by
  have hp (i : Fin N) : particlePosition (permutePositions σ X) i =
      particlePosition X (σ i) := rfl
  simp only [ionizationSumWeight, ionizationParticleWeight, hp]
  exact Equiv.sum_comp σ (fun i => ionizationWeight ε ‖particlePosition X i‖)

/-- An individual weighted state, with no assertion of antisymmetry. -/
@[expose] noncomputable def ionizationParticleState {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i : Fin N) (u : State N q) : State N q :=
  lipschitzBoundedSMul (ionizationParticleWeight ε i) ε⁻¹
    (norm_ionizationParticleWeight_le ε hε i)
    (lipschitzWith_ionizationParticleWeight ε hε.le i) u

theorem ionizationParticleState_coeFn {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (i : Fin N) (u : State N q) :
    ⇑(ionizationParticleState ε hε i u) =ᵐ[volume]
      fun X => (ionizationParticleWeight ε i X : ℂ) • u X :=
  lipschitzBoundedSMul_coeFn _ _ _ _ _

theorem kineticEnergy_ionizationParticleState_lt_top {N q : ℕ}
    (ε : ℝ) (hε : 0 < ε) (i : Fin N) (u : State N q)
    (hu : kineticEnergy u < ⊤) : kineticEnergy (ionizationParticleState ε hε i u) < ⊤ :=
  kineticEnergy_lipschitzBoundedSMul_lt_top u hu _ _ _ _ _

/-- Multiplication by the bounded sum weight. -/
@[expose] noncomputable def ionizationSumState {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (u : State N q) : State N q :=
  lipschitzBoundedSMul (ionizationSumWeight ε) ((N : ℝ) * ε⁻¹)
    (norm_ionizationSumWeight_le ε hε) (lipschitzWith_ionizationSumWeight ε hε.le) u

theorem ionizationSumState_coeFn {N q : ℕ} (ε : ℝ) (hε : 0 < ε) (u : State N q) :
    ⇑(ionizationSumState ε hε u) =ᵐ[volume]
      fun X => (ionizationSumWeight ε X : ℂ) • u X :=
  lipschitzBoundedSMul_coeFn _ _ _ _ _

theorem ionizationSumState_eq_sum {N q : ℕ} (ε : ℝ) (hε : 0 < ε) (u : State N q) :
    ionizationSumState ε hε u = ∑ i : Fin N, ionizationParticleState ε hε i u := by
  apply Lp.ext
  have hi := ae_all_iff.mpr (fun i => ionizationParticleState_coeFn ε hε i u)
  filter_upwards [ionizationSumState_coeFn ε hε u,
    Lp.coeFn_finsetSum Finset.univ (fun i => ionizationParticleState ε hε i u), hi]
    with X hs ht hi
  rw [hs, ht]
  simp only [Finset.sum_apply, hi, ionizationSumWeight, Complex.ofReal_sum, Finset.sum_smul]

theorem antisymmetric_ionizationSumState {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (u : State N q) (hu : antisymmetric u) : antisymmetric (ionizationSumState ε hε u) := by
  intro σ
  have h := ionizationSumState_coeFn ε hε u
  filter_upwards [hu σ, h,
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae h] with X huX hX hσX
  intro s
  rw [hσX, hX, ionizationSumWeight_permutePositions]
  simp only [PiLp.smul_apply, smul_eq_mul, huX]
  ring

/-- The actual admissible cutoff pair estimate test in the antisymmetric form domain. -/
@[expose] noncomputable def ionizationSumFormTest {N q : ℕ} (ε : ℝ) (hε : 0 < ε)
    (u : FormDomain N q) : FormDomain N q :=
  ⟨ionizationSumState ε hε (u : State N q),
    antisymmetric_ionizationSumState ε hε _ u.property.1,
    kineticEnergy_lipschitzBoundedSMul_lt_top _ u.property.2 _ _ _ _ _⟩

end LiebThirring
end
