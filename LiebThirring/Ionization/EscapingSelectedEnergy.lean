/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingAttraction

/-! # Integrated variational comparison for a partially antisymmetric particle block

All outside positions and spins are disintegrated before applying the k-electron
variational bound. The outside kinetic energy and repulsion remain nonnegative.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Classical

namespace LiebThirring
open Sobolev Variational

/-- The summed squared masses of the selected slices are integrable. -/
theorem integrable_sum_subsetParticleSlice_norm_sq {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (v : State N q) :
    Integrable (fun y : SubsetSpectatorConfiguration S =>
      ∑ α : SubsetSpectatorSpins S q, ‖subsetParticleSlice S e v y α‖ ^ 2) := by
  apply integrable_finsetSum Finset.univ
  intro α _
  apply (Lp.memLp (subsetSliceFieldCLM S e α v)).integrable_norm_pow (by norm_num) |>.congr
  filter_upwards [subsetSliceFieldCLM_ae S e α v] with y hy
  rw [hy]

/-- The k-electron variational threshold bounds a blockwise antisymmetric state after
integrating over all complementary positions and spins. -/
theorem atomicGroundStateEnergy_mul_norm_sq_le_selectedEnergy_of_finite (q : ℕ) (hq : 1 ≤ q)
    {N k : ℕ} (Z : ℝ≥0) (S : Set (Fin N)) (e : Fin k ≃ S)
    (v : State N q) (hvkin : kineticEnergy v < ⊤)
    (hv : ∀ σ : Equiv.Perm (Fin N), (∀ i, i ∈ (S : Set (Fin N)) ↔ σ i ∈ (S : Set (Fin N))) →
      ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
        v (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * v x s)
    (hrepfin : (∫⁻ X : Configuration N, electronRepulsion
      (((subsetOrderedInsertion S e).symm X).2) * ‖v X‖ₑ ^ 2) < ⊤)
    (hattrfin : (∫⁻ X : Configuration N, attraction (fun _ : Fin 1 => Z) (fun _ => 0)
      (((subsetOrderedInsertion S e).symm X).2) * ‖v X‖ₑ ^ 2) < ⊤) :
    (atomicGroundStateEnergy k q Z).toReal * ‖v‖ ^ 2 ≤ (kineticEnergy v).toReal +
      (∫⁻ X : Configuration N, electronRepulsion
        (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2).toReal -
      (∫⁻ X : Configuration N, attraction (fun _ : Fin 1 => Z) (fun _ => 0)
        (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2).toReal := by
  classical
  let block : Set (Fin N) := S
  let z : Fin 1 → ℝ≥0 := fun _ => Z
  let pos : Fin 1 → Position := fun _ => 0
  let rep : SubsetSpectatorConfiguration block × Configuration k → ℝ≥0∞ :=
    fun x => electronRepulsion x.2
  let attr : SubsetSpectatorConfiguration block × Configuration k → ℝ≥0∞ :=
    fun x => attraction z pos x.2
  have hrepmeas : Measurable rep := Assembly.measurable_electronRepulsion.comp measurable_snd
  have hattrmeas : Measurable attr := (measurable_attraction z pos).comp measurable_snd
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top v hvkin
  have hki := integrable_subsetParticleSlice_kineticEnergy_toReal block e v g hg
  have hr := integrable_subsetParticleSlice_expectation block e v rep hrepmeas hrepfin
  have ha := integrable_subsetParticleSlice_expectation block e v attr hattrmeas hattrfin
  have hnuc : nuclearRepulsion z pos = 0 := by simp only [z, pos, nuclearRepulsion]; simp
  have hs : Integrable (fun y : SubsetSpectatorConfiguration block =>
      ∑ α : SubsetSpectatorSpins block q, fullRealEnergy z pos
        (subsetParticleSlice block e v y α)) := by
    apply ((hki.add hr).sub ha).congr
    filter_upwards [] with y
    simp only [fullRealEnergy, hnuc, ENNReal.toReal_zero, zero_mul, add_zero,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Pi.add_apply, Pi.sub_apply, rep, attr]
  have hpoint : ∀ᵐ y : SubsetSpectatorConfiguration block,
      (atomicGroundStateEnergy k q Z).toReal *
        (∑ α : SubsetSpectatorSpins block q, ‖subsetParticleSlice block e v y α‖ ^ 2) ≤
      ∑ α : SubsetSpectatorSpins block q,
        fullRealEnergy z pos (subsetParticleSlice block e v y α) := by
    filter_upwards [stabilizerSubsetParticleFormSlice_ae block e v hvkin hv] with y hy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    have h := atomicGroundStateEnergy_mul_norm_sq_le_stabilizerSliceEnergy q hq Z block e v y α
    rw [hy α] at h
    exact h
  have hi := integral_mono_ae
    ((integrable_sum_subsetParticleSlice_norm_sq block e v).const_mul
      (atomicGroundStateEnergy k q Z).toReal) hs hpoint
  rw [integral_const_mul, integral_subsetParticleSlice_norm_sq] at hi
  have he : (∫ y : SubsetSpectatorConfiguration block,
      ∑ α : SubsetSpectatorSpins block q,
        fullRealEnergy z pos (subsetParticleSlice block e v y α)) =
      (∫ y : SubsetSpectatorConfiguration block,
        ∑ α : SubsetSpectatorSpins block q,
          (kineticEnergy (subsetParticleSlice block e v y α)).toReal) +
      (∫⁻ X : Configuration N, rep ((subsetOrderedInsertion block e).symm X) * ‖v X‖ₑ ^ 2).toReal -
      (∫⁻ X : Configuration N, attr ((subsetOrderedInsertion block e).symm X) * ‖v X‖ₑ ^ 2).toReal := by
    have hsplit := integral_sub (hki.add hr) ha
    simp only [Pi.add_apply] at hsplit
    rw [integral_add hki hr,
      integral_subsetParticleSlice_expectation block e v rep hrepmeas hrepfin,
      integral_subsetParticleSlice_expectation block e v attr hattrmeas hattrfin] at hsplit
    simpa only [fullRealEnergy, hnuc, ENNReal.toReal_zero, zero_mul, add_zero,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Pi.add_apply, Pi.sub_apply, rep, attr]
      using hsplit
  rw [he] at hi
  exact hi.trans (sub_le_sub
    (add_le_add (integral_subsetParticleSlice_kineticEnergy_toReal_le block e v hvkin) le_rfl) le_rfl)

/-- Finite kinetic energy discharges both selected Coulomb finiteness premises in the
integrated block variational comparison. -/
theorem atomicGroundStateEnergy_mul_norm_sq_le_selectedEnergy (q : ℕ) (hq : 1 ≤ q)
    {N k : ℕ} (Z : ℝ≥0) (S : Finset (Fin N)) (e : Fin k ≃ (S : Set (Fin N)))
    (v : State N q) (hvkin : kineticEnergy v < ⊤)
    (hv : ∀ σ : Equiv.Perm (Fin N), (∀ i, i ∈ (S : Set (Fin N)) ↔ σ i ∈ (S : Set (Fin N))) →
      ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ s : SpinLabels N q,
        v (permutePositions σ x) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * v x s) :
    (atomicGroundStateEnergy k q Z).toReal * ‖v‖ ^ 2 ≤ (kineticEnergy v).toReal +
      (∫⁻ X : Configuration N, electronRepulsion
        (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2).toReal -
      (∫⁻ X : Configuration N, attraction (fun _ : Fin 1 => Z) (fun _ => 0)
        (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2).toReal :=
  atomicGroundStateEnergy_mul_norm_sq_le_selectedEnergy_of_finite q hq Z (S : Set (Fin N))
    e v hvkin hv
    ((lintegral_subsetSelectedRepulsion_le (S : Set (Fin N)) e v).trans_lt
      (lintegral_electronRepulsion_lt_top v hvkin))
    (lintegral_selected_attraction_lt_top Z S e v hvkin)

end LiebThirring
end
