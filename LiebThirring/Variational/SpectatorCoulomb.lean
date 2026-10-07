/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorKernels
public import LiebThirring.Variational.SpectatorReindex
public import LiebThirring.Variational.FormFinite

/-!
# Coulomb reconstruction from selected and residual coordinates

The selected position and explicitly reindexed residual configuration reconstruct the original
configuration exactly. Consequently the full repulsive and atomic attractive kernels split into
their residual and selected-particle terms at every configuration, including collisions.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Variational

/-- Sum of the selected particle's repulsive interactions with the ordered residual particles. -/
@[expose] noncomputable def selectedRepulsionKernel {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (X : Configuration (N + 1)) : ℝ≥0∞ :=
  ∑ j : Fin N, coulombKernel (particlePosition X i)
    (particlePosition (residualProjection i e X) j)

/-- Selected position and residual projection reconstruct a full configuration. -/
theorem spectatorInsert_particlePosition_residualProjection {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (X : Configuration (N + 1)) :
    spectatorInsert i e (particlePosition X i) (residualProjection i e X) = X := by
  unfold spectatorInsert residualProjection
  rw [(Sobolev.configurationReindexMeasurableEquiv e).apply_symm_apply]
  rw [← insertionMeasurableEquiv_symm_fst i X]
  rw [← insertionMeasurableEquiv_apply]
  exact (insertionMeasurableEquiv i).apply_symm_apply X

/-- A residual coordinate of spectator insertion is the corresponding residual position. -/
theorem particlePosition_spectatorInsert_residual {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (x : Position)
    (y : Configuration N) (j : Fin N) :
    particlePosition (spectatorInsert i e x y) (e j).val = particlePosition y j := by
  ext a
  simp only [particlePosition, spectatorInsert, insertParticle, PiLp.toLp_apply,
    dite_eq_right (e j).property]
  exact configurationReindex_apply i e y j a

/-- Residual projection reads the original position at the index specified by the ordering. -/
theorem particlePosition_residualProjection {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (X : Configuration (N + 1))
    (j : Fin N) :
    particlePosition (residualProjection i e X) j = particlePosition X (e j).val := by
  have hrec := spectatorInsert_particlePosition_residualProjection i e X
  have hp := congrArg (fun Y : Configuration (N + 1) => particlePosition Y (e j).val) hrec
  rw [particlePosition_spectatorInsert_residual] at hp
  exact hp

/-- The selected repulsion kernel can be written entirely in original full coordinates. -/
theorem selectedRepulsionKernel_eq_sum_full {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (X : Configuration (N + 1)) :
    selectedRepulsionKernel i e X =
      ∑ j : Fin N, coulombKernel (particlePosition X i) (particlePosition X (e j).val) := by
  unfold selectedRepulsionKernel
  apply Finset.sum_congr rfl
  intro j _
  rw [particlePosition_residualProjection]

/-- The selected-particle repulsion kernel is measurable without composing through the residual
projection map. -/
theorem measurable_selectedRepulsionKernel {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) :
    Measurable (selectedRepulsionKernel i e) := by
  have hi : Measurable (fun X : Configuration (N + 1) => particlePosition X i) :=
    measurable_particlePosition i
  have hj (j : Fin N) :
      Measurable (fun X : Configuration (N + 1) => particlePosition X (e j).val) :=
    measurable_particlePosition (e j).val
  have hc (j : Fin N) : Measurable (fun X : Configuration (N + 1) =>
      coulombKernel (particlePosition X i) (particlePosition X (e j).val)) :=
    ((hi.sub (hj j)).norm.ennreal_ofReal).inv
  have hmeas : Measurable (fun X : Configuration (N + 1) =>
      ∑ j : Fin N, coulombKernel (particlePosition X i) (particlePosition X (e j).val)) :=
    Finset.measurable_sum _ fun j _ => hc j
  have heq : selectedRepulsionKernel i e = fun X : Configuration (N + 1) =>
      ∑ j : Fin N, coulombKernel (particlePosition X i) (particlePosition X (e j).val) := by
    funext X
    exact selectedRepulsionKernel_eq_sum_full i e X
  rw [heq]
  exact hmeas

/-- Full electron repulsion is residual repulsion plus all interactions with the selected
particle. -/
theorem electronRepulsion_residualProjection {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (X : Configuration (N + 1)) :
    electronRepulsion X = electronRepulsion (residualProjection i e X) +
      ∑ j : Fin N, coulombKernel (particlePosition X i)
        (particlePosition (residualProjection i e X) j) := by
  have hrec := spectatorInsert_particlePosition_residualProjection i e X
  calc
    electronRepulsion X = electronRepulsion
        (spectatorInsert i e (particlePosition X i) (residualProjection i e X)) :=
      congrArg electronRepulsion hrec.symm
    _ = _ := electronRepulsion_spectatorInsert i e _ _

/-- Full atomic attraction is residual attraction plus the selected particle's attraction. -/
theorem attraction_atom_residualProjection {N : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (X : Configuration (N + 1)) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) X =
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) (residualProjection i e X) +
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0 := by
  have hrec := spectatorInsert_particlePosition_residualProjection i e X
  calc
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) X =
        attraction (fun _ : Fin 1 => Z) (fun _ => 0)
          (spectatorInsert i e (particlePosition X i) (residualProjection i e X)) :=
      congrArg (attraction (fun _ : Fin 1 => Z) (fun _ => 0)) hrec.symm
    _ = _ := attraction_spectatorInsert_atom i e Z _ _

/-- The full finite repulsive expectation controls its residual part. -/
theorem lintegral_residual_repulsion_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q) :
    (∫⁻ X, electronRepulsion (residualProjection i e X) *
      ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ := by
  apply (lintegral_mono fun X => ?_).trans_lt
    (lintegral_electronRepulsion_lt_top (u : State (N + 1) q) u.property.2)
  apply mul_le_mul_of_nonneg_right
  · rw [electronRepulsion_residualProjection i e X]
    exact le_add_right le_rfl
  · exact bot_le

/-- The full finite repulsive expectation controls the selected particle interactions. -/
theorem lintegral_selected_repulsion_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q) :
    (∫⁻ X, (∑ j : Fin N, coulombKernel (particlePosition X i)
      (particlePosition (residualProjection i e X) j)) *
        ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ := by
  apply (lintegral_mono fun X => ?_).trans_lt
    (lintegral_electronRepulsion_lt_top (u : State (N + 1) q) u.property.2)
  apply mul_le_mul_of_nonneg_right
  · rw [electronRepulsion_residualProjection i e X]
    exact le_add_left le_rfl
  · exact bot_le

/-- The full finite atomic attraction controls its residual attraction. -/
theorem lintegral_residual_attraction_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) :
    (∫⁻ X, attraction (fun _ : Fin 1 => Z) (fun _ => 0) (residualProjection i e X) *
      ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ := by
  apply (lintegral_mono fun X => ?_).trans_lt
    (lintegral_attraction_lt_top (fun _ : Fin 1 => Z) (fun _ => 0)
      (u : State (N + 1) q) u.property.2)
  apply mul_le_mul_of_nonneg_right
  · rw [attraction_atom_residualProjection i e Z X]
    exact le_add_right le_rfl
  · exact bot_le

/-- The full finite atomic attraction controls the selected particle attraction. -/
theorem lintegral_selected_attraction_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) :
    (∫⁻ X, ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) *
      ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ := by
  apply (lintegral_mono fun X => ?_).trans_lt
    (lintegral_attraction_lt_top (fun _ : Fin 1 => Z) (fun _ => 0)
      (u : State (N + 1) q) u.property.2)
  apply mul_le_mul_of_nonneg_right
  · rw [attraction_atom_residualProjection i e Z X]
    exact le_add_left le_rfl
  · exact bot_le

/-- A bounded selected-position weight preserves finiteness of residual repulsion. -/
theorem lintegral_weighted_residual_repulsion_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q)
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫⁻ X, ENNReal.ofReal (b (particlePosition X i)) *
      electronRepulsion (residualProjection i e X) * ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ :=
  lintegral_bounded_weight_lt_top (fun X => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) _ _ (lintegral_residual_repulsion_lt_top i e u)

/-- A bounded selected-position weight preserves finiteness of selected repulsion. -/
theorem lintegral_weighted_selected_repulsion_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q)
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫⁻ X, ENNReal.ofReal (b (particlePosition X i)) *
      (∑ j : Fin N, coulombKernel (particlePosition X i)
        (particlePosition (residualProjection i e X) j)) *
          ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ :=
  lintegral_bounded_weight_lt_top (fun X => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) _ _ (lintegral_selected_repulsion_lt_top i e u)

/-- A bounded selected-position weight preserves finiteness of residual attraction. -/
theorem lintegral_weighted_residual_attraction_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (B : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫⁻ X, ENNReal.ofReal (b (particlePosition X i)) *
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) (residualProjection i e X) *
        ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ :=
  lintegral_bounded_weight_lt_top (fun X => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) _ _
      (lintegral_residual_attraction_lt_top i e Z u)

/-- A bounded selected-position weight preserves finiteness of selected attraction. -/
theorem lintegral_weighted_selected_attraction_lt_top {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (B : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫⁻ X, ENNReal.ofReal (b (particlePosition X i)) *
      ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) *
        ‖(u : State (N + 1) q) X‖ₑ ^ 2) < ⊤ :=
  lintegral_bounded_weight_lt_top (fun X => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) _ _
      (lintegral_selected_attraction_lt_top i e Z u)

end LiebThirring.Variational

end
