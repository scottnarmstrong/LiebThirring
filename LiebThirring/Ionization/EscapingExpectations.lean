/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubsetEnergy

/-! # Nonnegative expectation disintegration for arbitrary particle subsets

This is the subset version of spectator disintegration used in the escaping-sector comparison. All complementary spin
assignments remain in the outer finite sum.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Classical

namespace LiebThirring.Variational

/-- Integrating the selected-block kinetic energy discards only nonnegative outside
derivative energies. No symmetry of the full state is required. -/
theorem integral_subsetParticleSlice_kineticEnergy_toReal_le {N k q : ℕ}
    (S : Set (Fin N)) (e : Fin k ≃ S) (u : State N q) (hu : kineticEnergy u < ⊤) :
    (∫ y : SubsetSpectatorConfiguration S, ∑ α : SubsetSpectatorSpins S q,
      (kineticEnergy (subsetParticleSlice S e u y α)).toReal) ≤ (kineticEnergy u).toReal := by
  obtain ⟨g, hg⟩ := Sobolev.exists_weakDerivatives_of_kineticEnergy_lt_top u hu
  rw [integral_subsetParticleSlice_kineticEnergy_toReal S e u g hg,
    Sobolev.kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq u g hg,
    Fintype.sum_prod_type]
  apply Finset.sum_le_sum_of_injOn (fun j : Fin k => (e j).val)
    (fun _ _ _ _ h => e.injective (Subtype.ext h))
  · exact Finset.subset_univ _
  · intro _ _
    exact le_rfl
  · intro _ _ _
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The slice representatives preserve the full pointwise mass after spin regrouping. -/
theorem subsetParticleSlice_spin_mass_ae {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ᵐ x : Configuration k,
      ‖u (subsetOrderedInsertion S e (y, x))‖ₑ ^ 2 =
        ∑ α : SubsetSpectatorSpins S q, ‖subsetParticleSlice S e u y α x‖ₑ ^ 2 := by
  filter_upwards [subsetParticleSlice_ae S e u] with y hy
  have hxy := ae_all_iff.mpr hy
  filter_upwards [hxy] with x hx
  rw [← (subsetSpinCurrying (q := q) S e).enorm_map, piLp_enorm_sq]
  apply Finset.sum_congr rfl
  intro α _
  have heq : subsetSpinCurrying S e (u (subsetOrderedInsertion S e (y, x))) α =
      subsetParticleSlice S e u y α x := by
    ext s
    exact (hx α s).symm
  rw [heq]

/-- Tonelli disintegration of every nonnegative quadratic expectation over an ordered
particle subset and all complementary spins. -/
theorem lintegral_subsetParticleSlice_weight {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q)
    (p : SubsetSpectatorConfiguration S × Configuration k → ℝ≥0∞)
    (hp : Measurable p) :
    (∫⁻ X : Configuration N,
      p ((subsetOrderedInsertion S e).symm X) * ‖u X‖ₑ ^ 2) =
      ∫⁻ y : SubsetSpectatorConfiguration S, ∑ α : SubsetSpectatorSpins S q,
        ∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2 := by
  let F : Configuration N → ℝ≥0∞ := fun X =>
    p ((subsetOrderedInsertion S e).symm X) * ‖u X‖ₑ ^ 2
  have hF : Measurable F :=
    (hp.comp (subsetOrderedInsertion S e).symm.measurable).mul
      ((Lp.stronglyMeasurable u).enorm.pow_const 2)
  calc
    _ = ∫⁻ z : SubsetSpectatorConfiguration S × Configuration k,
        F (subsetOrderedInsertion S e z) :=
      ((measurePreserving_subsetOrderedInsertion S e).lintegral_comp hF).symm
    _ = ∫⁻ y : SubsetSpectatorConfiguration S, ∫⁻ x : Configuration k,
        p (y, x) * ‖u (subsetOrderedInsertion S e (y, x))‖ₑ ^ 2 := by
      have ht := lintegral_prod (μ := (volume : Measure (SubsetSpectatorConfiguration S)))
        (ν := (volume : Measure (Configuration k)))
        (fun z => F (subsetOrderedInsertion S e z))
        (hF.comp (subsetOrderedInsertion S e).measurable).aemeasurable
      simpa only [F, MeasurableEquiv.symm_apply_apply, Measure.volume_eq_prod] using ht
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [subsetParticleSlice_spin_mass_ae S e u] with y hy
      calc
        _ = ∫⁻ x : Configuration k, ∑ α : SubsetSpectatorSpins S q,
            p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2 := by
          apply lintegral_congr_ae
          filter_upwards [hy] with x hx
          rw [hx, Finset.mul_sum]
        _ = _ := lintegral_finsetSum _ (fun α _ =>
          ((hp.comp (measurable_const.prodMk measurable_id)).mul
            ((Lp.stronglyMeasurable (subsetParticleSlice S e u y α)).enorm.pow_const 2)))

/-- Outer slice expectations are measurable up to the representative ambiguity. -/
theorem aemeasurable_subsetParticleSlice_expectation {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q)
    (p : SubsetSpectatorConfiguration S × Configuration k → ℝ≥0∞)
    (hp : Measurable p) :
    AEMeasurable (fun y : SubsetSpectatorConfiguration S =>
      ∑ α : SubsetSpectatorSpins S q,
        ∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2) := by
  let F := fun (α : SubsetSpectatorSpins S q)
      (z : SubsetSpectatorConfiguration S × Configuration k) =>
    p z * ‖subsetSpinCurrying S e (u (subsetOrderedInsertion S e z)) α‖ₑ ^ 2
  have hF (α : SubsetSpectatorSpins S q) : Measurable (F α) := by
    apply hp.mul
    apply Measurable.pow_const
    apply Measurable.enorm
    have hcur := (subsetSpinCurrying (q := q) S e).continuous.measurable.comp
      ((Lp.stronglyMeasurable u).measurable.comp (subsetOrderedInsertion S e).measurable)
    exact (PiLp.continuous_apply 2 _ α).measurable.comp hcur
  have hm : Measurable (fun y : SubsetSpectatorConfiguration S =>
      ∑ α : SubsetSpectatorSpins S q, ∫⁻ x : Configuration k, F α (y, x)) :=
    Finset.measurable_sum _ (fun α _ => (hF α).lintegral_prod_right')
  apply hm.aemeasurable.congr
  filter_upwards [subsetParticleSlice_ae S e u] with y hy
  apply Finset.sum_congr rfl
  intro α _
  apply lintegral_congr_ae
  filter_upwards [hy α] with x hx
  have heq : subsetSpinCurrying S e (u (subsetOrderedInsertion S e (y, x))) α =
      subsetParticleSlice S e u y α x := by
    ext s
    exact (hx s).symm
  exact congrArg (fun v : SpinAmplitudes k q => p (y, x) * ‖v‖ₑ ^ 2) heq

/-- A finite full expectation makes the summed real slice expectations integrable. -/
theorem integrable_subsetParticleSlice_expectation {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q)
    (p : SubsetSpectatorConfiguration S × Configuration k → ℝ≥0∞)
    (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p ((subsetOrderedInsertion S e).symm X) * ‖u X‖ₑ ^ 2) < ⊤) :
    Integrable (fun y : SubsetSpectatorConfiguration S => ∑ α : SubsetSpectatorSpins S q,
      (∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2).toReal) := by
  have hm := aemeasurable_subsetParticleSlice_expectation S e u p hp
  have hf : (∫⁻ y : SubsetSpectatorConfiguration S, ∑ α : SubsetSpectatorSpins S q,
      ∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2) < ⊤ := by
    rw [← lintegral_subsetParticleSlice_weight S e u p hp]
    exact hfin
  apply (integrable_toReal_of_lintegral_ne_top hm hf.ne).congr
  filter_upwards [ae_lt_top' hm hf.ne] with y hy
  exact ENNReal.toReal_sum (fun α _ =>
    (lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ α)) hy).ne)

/-- Exact finite real disintegration over all complementary spin assignments. -/
theorem integral_subsetParticleSlice_expectation {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q)
    (p : SubsetSpectatorConfiguration S × Configuration k → ℝ≥0∞)
    (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p ((subsetOrderedInsertion S e).symm X) * ‖u X‖ₑ ^ 2) < ⊤) :
    (∫ y : SubsetSpectatorConfiguration S, ∑ α : SubsetSpectatorSpins S q,
      (∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2).toReal) =
    (∫⁻ X : Configuration N,
      p ((subsetOrderedInsertion S e).symm X) * ‖u X‖ₑ ^ 2).toReal := by
  have hm := aemeasurable_subsetParticleSlice_expectation S e u p hp
  have hf : (∫⁻ y : SubsetSpectatorConfiguration S, ∑ α : SubsetSpectatorSpins S q,
      ∫⁻ x : Configuration k, p (y, x) * ‖subsetParticleSlice S e u y α x‖ₑ ^ 2) < ⊤ := by
    rw [← lintegral_subsetParticleSlice_weight S e u p hp]
    exact hfin
  rw [lintegral_subsetParticleSlice_weight S e u p hp]
  rw [← integral_toReal hm (ae_lt_top' hm hf.ne)]
  apply integral_congr_ae
  filter_upwards [ae_lt_top' hm hf.ne] with y hy
  exact (ENNReal.toReal_sum (fun α _ =>
    (lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ α)) hy).ne)).symm

end LiebThirring.Variational
end
