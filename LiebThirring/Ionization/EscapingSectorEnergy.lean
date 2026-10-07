/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingSelectedEnergy

/-! # Energy lower bounds for proper escaping IMS sectors -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring

open Sobolev Variational

/-- Every proper IMS sector lies above the one-electron-removal threshold, up to the
explicit attraction loss of its outside particles. -/
theorem fullRealEnergy_imsRampSector_ge_pred {N q : ℕ} (hq : 1 ≤ q) (Z : ℝ≥0)
    {R : ℝ} (hR : 0 < R) (u : FormDomain N q) (S : Finset (Fin N))
    (hS : S ≠ Finset.univ) :
    let v := imsLocalizedState hR S (u : State N q)
    ((atomicGroundStateEnergy (N - 1) q Z).toReal - (N : ℝ) * (Z : ℝ) / R) *
        ‖v‖ ^ 2 ≤
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0) v := by
  classical
  let e : Fin S.card ≃ (S : Set (Fin N)) := S.equivFin.symm
  let v := imsLocalizedState hR S (u : State N q)
  have hvkin : kineticEnergy v < ⊤ :=
    kineticEnergy_lipschitzBoundedSMul_lt_top (u : State N q) u.property.2 _ 1
      (norm_imsSectorWeight_le_one R S) _ (lipschitzWith_imsSectorWeight hR S)
  have hstab : ∀ σ : Equiv.Perm (Fin N), (∀ i, i ∈ S ↔ σ i ∈ S) →
      ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
        v (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * v x s := by
    intro σ hσ
    exact imsRampSector_permutation_identity hR (u : State N q) u.property.1 S σ hσ
  have hsel := atomicGroundStateEnergy_mul_norm_sq_le_selectedEnergy
    q hq Z S e v hvkin hstab
  have hrepE := lintegral_subsetSelectedRepulsion_le (S : Set (Fin N)) e v
  have hrepFull := lintegral_electronRepulsion_lt_top v hvkin
  have hrep :
      (∫⁻ X : Configuration N,
        electronRepulsion ((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2 *
          ‖v X‖ₑ ^ 2).toReal ≤
      (∫⁻ X : Configuration N, electronRepulsion X * ‖v X‖ₑ ^ 2).toReal :=
    ENNReal.toReal_mono hrepFull.ne hrepE
  have hatt := imsLocalizedState_attraction_le_selected_add_error hR Z S e
    (u : State N q) u.property.2
  have hcard : S.card < N := by
    simpa using Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hS⟩)
  have hthreshold := atomicGroundStateEnergy_toReal_pred_le_of_lt q hq Z hcard
  have hnuc : nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => (0 : Position)) = 0 := by
    simp only [nuclearRepulsion]
    simp
  unfold fullRealEnergy
  dsimp only [v] at hsel hrep hatt ⊢
  rw [hnuc, ENNReal.toReal_zero, zero_mul, add_zero, sub_mul]
  have hthreshold' := mul_le_mul_of_nonneg_right hthreshold
    (sq_nonneg ‖imsLocalizedState hR S (u : State N q)‖)
  linarith only [hsel, hrep, hatt, hthreshold']

end LiebThirring

end
