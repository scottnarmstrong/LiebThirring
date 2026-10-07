/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubsetForm
public import LiebThirring.Variational.SpectatorEnergy

/-! # Selected kinetic-energy disintegration for arbitrary particle blocks -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring.Variational

open Sobolev

private theorem integral_l2_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} (v : Lp E 2 μ) :
    (∫ x : X, ‖v x‖ ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  have hfin : (∫⁻ x : X, (1 : ℝ≥0∞) * ‖v x‖ₑ ^ 2 ∂μ) < ⊤ := by
    simp only [one_mul, lintegral_l2_enorm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  have h := LiebThirring.integral_weight_norm_sq
    (p := fun _ : X => (1 : ℝ≥0∞)) (f := fun x => v x)
    measurable_const.aemeasurable (Lp.aestronglyMeasurable v) hfin
  simp only [ENNReal.toReal_one, one_mul] at h
  change (∫ x : X, ‖v x‖ ^ 2 ∂μ) = (∫⁻ x : X, ‖v x‖ₑ ^ 2 ∂μ).toReal at h
  rw [lintegral_l2_enorm_sq, ENNReal.toReal_pow] at h
  exact h

theorem integral_subsetParticleSlice_norm_sq {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (v : State N q) :
    (∫ y : SubsetSpectatorConfiguration S,
      ∑ α : SubsetSpectatorSpins S q, ‖subsetParticleSlice S e v y α‖ ^ 2) = ‖v‖ ^ 2 := by
  rw [integral_finsetSum]
  · calc
      (∑ α : SubsetSpectatorSpins S q,
          ∫ y, ‖subsetParticleSlice S e v y α‖ ^ 2) =
          ∑ α : SubsetSpectatorSpins S q,
            ∫ y, ‖subsetSliceFieldCLM S e α v y‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro α _
        apply integral_congr_ae
        filter_upwards [subsetSliceFieldCLM_ae S e α v] with y hy
        exact congrArg (fun z : State k q => ‖z‖ ^ 2) hy.symm
      _ = ∑ α : SubsetSpectatorSpins S q, ‖subsetSliceFieldCLM S e α v‖ ^ 2 := by
        simp_rw [integral_l2_norm_sq]
      _ = ‖v‖ ^ 2 := by
        change (∑ α : SubsetSpectatorSpins S q,
          ‖((finiteLpPiLpEquiv (volume : Measure (SubsetSpectatorConfiguration S))
            (fun _ : SubsetSpectatorSpins S q => State k q))
              (subsetParticleField S e v)) α‖ ^ 2) = _
        rw [← PiLp.norm_sq_eq_of_L2, LinearIsometryEquiv.norm_map,
          LinearIsometryEquiv.norm_map]
  · intro α _
    apply (Lp.memLp (subsetSliceFieldCLM S e α v)).integrable_norm_pow (by norm_num) |>.congr
    filter_upwards [subsetSliceFieldCLM_ae S e α v] with y hy
    rw [hy]

private theorem integral_sum_subsetParticleSlice_norm_sq {ι : Type*} [Fintype ι]
    {N k q : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S) (v : ι → State N q) :
    (∫ y : SubsetSpectatorConfiguration S, ∑ r : ι,
      ∑ α : SubsetSpectatorSpins S q, ‖subsetParticleSlice S e (v r) y α‖ ^ 2) =
      ∑ r : ι, ‖v r‖ ^ 2 := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun r _ => integral_subsetParticleSlice_norm_sq S e (v r)
  · intro r _
    apply integrable_finsetSum Finset.univ
    intro α _
    apply (Lp.memLp (subsetSliceFieldCLM S e α (v r))).integrable_norm_pow (by norm_num) |>.congr
    filter_upwards [subsetSliceFieldCLM_ae S e α (v r)] with y hy
    rw [hy]

/-- Pointwise selected-block kinetic energy is its weak-gradient square sum. -/
theorem subsetParticleSlice_kineticEnergy_toReal_ae {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      (kineticEnergy (subsetParticleSlice S e u y α)).toReal =
        ∑ a : Fin k × Fin 3,
          ‖subsetParticleSlice S e (g ((e a.1).val, a.2)) y α‖ ^ 2 := by
  filter_upwards [hasWeakDerivative_subsetParticleSlice_ae S e u g hg] with y hy
  intro α
  exact kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq _ _ (hy α)

/-- Selected kinetic energy disintegrates over all complementary configurations and spins. -/
theorem integral_subsetParticleSlice_kineticEnergy_toReal {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    (∫ y : SubsetSpectatorConfiguration S,
      ∑ α : SubsetSpectatorSpins S q,
        (kineticEnergy (subsetParticleSlice S e u y α)).toReal) =
      ∑ j : Fin k, ∑ a : Fin 3, ‖g ((e j).val, a)‖ ^ 2 := by
  rw [← Fintype.sum_prod_type
      (fun a : Fin k × Fin 3 => ‖g ((e a.1).val, a.2)‖ ^ 2),
    ← integral_sum_subsetParticleSlice_norm_sq S e
      (fun a : Fin k × Fin 3 => g ((e a.1).val, a.2))]
  apply integral_congr_ae
  filter_upwards [subsetParticleSlice_kineticEnergy_toReal_ae S e u g hg] with y hy
  simp_rw [hy]
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ α : SubsetSpectatorSpins S q, ∑ j : Fin k, ∑ a : Fin 3,
        ‖subsetParticleSlice S e (g ((e j).val, a)) y α‖ ^ 2) =
        ∑ j : Fin k, ∑ α : SubsetSpectatorSpins S q, ∑ a : Fin 3,
          ‖subsetParticleSlice S e (g ((e j).val, a)) y α‖ ^ 2 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

/-- The outer sum of selected-block kinetic energies is integrable. -/
theorem integrable_subsetParticleSlice_kineticEnergy_toReal {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    Integrable (fun y : SubsetSpectatorConfiguration S =>
      ∑ α : SubsetSpectatorSpins S q,
        (kineticEnergy (subsetParticleSlice S e u y α)).toReal) := by
  have hsum : Integrable (fun y : SubsetSpectatorConfiguration S =>
      ∑ j : Fin k, ∑ a : Fin 3, ∑ α : SubsetSpectatorSpins S q,
        ‖subsetParticleSlice S e (g ((e j).val, a)) y α‖ ^ 2) := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro a _
    apply integrable_finsetSum Finset.univ
    intro α _
    apply (Lp.memLp (subsetSliceFieldCLM S e α (g ((e j).val, a)))).integrable_norm_pow
      (by norm_num) |>.congr
    filter_upwards [subsetSliceFieldCLM_ae S e α (g ((e j).val, a))] with y hy
    rw [hy]
  apply hsum.congr
  filter_upwards [subsetParticleSlice_kineticEnergy_toReal_ae S e u g hg] with y hy
  simp_rw [hy, Fintype.sum_prod_type]
  calc
    (∑ j : Fin k, ∑ a : Fin 3, ∑ α : SubsetSpectatorSpins S q,
        ‖subsetParticleSlice S e (g ((e j).val, a)) y α‖ ^ 2) =
        ∑ j : Fin k, ∑ α : SubsetSpectatorSpins S q, ∑ a : Fin 3,
          ‖subsetParticleSlice S e (g ((e j).val, a)) y α‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

end LiebThirring.Variational
end
