/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorIntegral
public import LiebThirring.Variational.SlicesResidual

/-!
# Spectator disintegration on a reindexed residual configuration
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Variational

/-- Project a full configuration to the explicitly ordered residual configuration. -/
@[expose] noncomputable def residualProjection {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (X : Configuration N) : Configuration k :=
  (Sobolev.configurationReindexMeasurableEquiv e).symm
    (((insertionMeasurableEquiv i).symm X).2)

theorem measurable_residualProjection {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) : Measurable (residualProjection i e) :=
  (Sobolev.configurationReindexMeasurableEquiv e).symm.measurable.comp
    (measurable_snd.comp (insertionMeasurableEquiv i).symm.measurable)

/-- The first coordinate of the insertion inverse is the selected particle position. -/
theorem insertionMeasurableEquiv_symm_fst {N : ℕ} (i : Fin N) (X : Configuration N) :
    ((insertionMeasurableEquiv i).symm X).1 = particlePosition X i := by
  let z := (insertionMeasurableEquiv i).symm X
  have hX : insertParticle i z.1 z.2 = X := by
    rw [← insertionMeasurableEquiv_apply i z, MeasurableEquiv.apply_symm_apply]
  change z.1 = particlePosition X i
  calc
    z.1 = particlePosition (insertParticle i z.1 z.2) i :=
      (particlePosition_insertParticle i z.1 z.2).symm
    _ = _ := congrArg (fun Y => particlePosition Y i) hX

/-- Weighted quadratic mass is unchanged by reindexing a residual L² state. -/
theorem lintegral_residualStateReindex_weight {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (v : RestState i q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ y : OtherConfiguration i,
      p ((Sobolev.configurationReindexMeasurableEquiv e).symm y) * ‖v y‖ₑ ^ 2) =
      ∫⁻ y : Configuration k, p y * ‖residualStateReindex i e v y‖ₑ ^ 2 := by
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hnorm : ∀ᵐ y : Configuration k,
      ‖residualStateReindex i e v y‖ₑ = ‖v (E y)‖ₑ := by
    filter_upwards [residualStateReindex_ae i e v] with y hy
    rw [← (residualSpinReindex i e).enorm_map]
    congr 1
    ext s
    simpa [residualSpinReindex, residualSpinLabelEquiv] using hy s
  have hm : Measurable (fun y : OtherConfiguration i =>
      p (E.symm y) * ‖v y‖ₑ ^ 2) :=
    (hp.comp E.symm.measurable).mul ((Lp.stronglyMeasurable v).enorm.pow_const 2)
  calc
    _ = ∫⁻ y : Configuration k, p (E.symm (E y)) * ‖v (E y)‖ₑ ^ 2 :=
      ((Sobolev.measurePreserving_configurationReindex e).lintegral_comp hm).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hnorm] with y hy
      rw [E.symm_apply_apply, hy]

/-- Tonelli disintegration with the residual variables reindexed to `Configuration k`. -/
theorem lintegral_spectator_reindex_weight {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ X : Configuration N, p (residualProjection i e X) * ‖u X‖ₑ ^ 2) =
      ∫⁻ x : Position, ∑ s : Fin q, ∫⁻ y : Configuration k,
        p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2 := by
  rw [show (fun X : Configuration N => p (residualProjection i e X) * ‖u X‖ₑ ^ 2) =
      fun X => (p ∘ (Sobolev.configurationReindexMeasurableEquiv e).symm)
        (((insertionMeasurableEquiv i).symm X).2) * ‖u X‖ₑ ^ 2 by rfl,
    LiebThirring.lintegral_spectator_weight i u
      (p ∘ (Sobolev.configurationReindexMeasurableEquiv e).symm)
      (hp.comp (Sobolev.configurationReindexMeasurableEquiv e).symm.measurable)]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro s _
  exact lintegral_residualStateReindex_weight i e (oneParticleCurrying i u x s) p hp

/-- Joint selected-position/residual-coordinate Tonelli disintegration after reindexing. -/
theorem lintegral_spectator_reindex {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Position × Configuration k → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ X : Configuration N,
      p (particlePosition X i, residualProjection i e X) * ‖u X‖ₑ ^ 2) =
      ∫⁻ x : Position, ∑ s : Fin q, ∫⁻ y : Configuration k,
        p (x, y) * ‖residualParticleSlice i e u x s y‖ₑ ^ 2 := by
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hbase := LiebThirring.lintegral_spectator_spin i u
    (fun z : Position × OtherConfiguration i => p (z.1, E.symm z.2))
    (hp.comp (measurable_fst.prodMk (E.symm.measurable.comp measurable_snd)))
  rw [show (fun X : Configuration N =>
      p (((insertionMeasurableEquiv i).symm X).1,
        E.symm (((insertionMeasurableEquiv i).symm X).2)) * ‖u X‖ₑ ^ 2) =
      (fun X => p (particlePosition X i, residualProjection i e X) * ‖u X‖ₑ ^ 2) by
        funext X
        rw [insertionMeasurableEquiv_symm_fst]
        rfl] at hbase
  rw [hbase]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro s _
  exact lintegral_residualStateReindex_weight i e (oneParticleCurrying i u x s)
    (fun y => p (x, y)) (hp.comp (measurable_const.prodMk measurable_id))

/-- The reindexed sum of residual expectations is measurable up to null sets. -/
theorem spectator_reindex_expectation_aemeasurable {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p) :
    AEMeasurable (fun x : Position => ∑ s : Fin q, ∫⁻ y : Configuration k,
      p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2) volume := by
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hm := LiebThirring.spectator_spin_expectation_aemeasurable i u
    (fun z : Position × OtherConfiguration i => p (E.symm z.2))
    (hp.comp (E.symm.measurable.comp measurable_snd))
  apply hm.congr
  filter_upwards [] with x
  apply Finset.sum_congr rfl
  intro s _
  exact lintegral_residualStateReindex_weight i e (oneParticleCurrying i u x s) p hp

/-- Finiteness of the full expectation gives finite reindexed residual expectations almost
everywhere, in every selected-spin sector. -/
theorem spectator_reindex_expectation_lt_top_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p (residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      (∫⁻ y : Configuration k,
        p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2) < ⊤ := by
  rw [lintegral_spectator_reindex_weight i e u p hp] at hfin
  have hs := ae_lt_top' (spectator_reindex_expectation_aemeasurable i e u p hp) hfin.ne
  filter_upwards [hs] with x hx
  intro s
  exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s)).trans_lt hx

/-- The outer integral of the literal real reindexed residual expectations is integrable. -/
theorem integrable_spectator_reindex_real {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p (residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤) :
    Integrable (fun x : Position => ∑ s : Fin q, ∫ y : Configuration k,
      (p y).toReal * ‖residualParticleSlice i e u x s y‖ ^ 2) := by
  have hslice := spectator_reindex_expectation_lt_top_ae i e u p hp hfin
  have hsum := integrable_toReal_of_lintegral_ne_top
    (spectator_reindex_expectation_aemeasurable i e u p hp)
    (by rw [← lintegral_spectator_reindex_weight i e u p hp]; exact hfin.ne)
  apply hsum.congr
  filter_upwards [hslice] with x hx
  rw [ENNReal.toReal_sum (fun s _ => (hx s).ne)]
  apply Finset.sum_congr rfl
  intro s _
  exact (LiebThirring.integral_weight_norm_sq hp.aemeasurable
    (Lp.aestronglyMeasurable (residualParticleSlice i e u x s)) (hx s)).symm

/-- The joint-kernel residual expectation is measurable up to null sets. -/
theorem spectator_reindex_joint_expectation_aemeasurable {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Position × Configuration k → ℝ≥0∞) (hp : Measurable p) :
    AEMeasurable (fun x : Position => ∑ s : Fin q, ∫⁻ y : Configuration k,
      p (x, y) * ‖residualParticleSlice i e u x s y‖ₑ ^ 2) volume := by
  let E := Sobolev.configurationReindexMeasurableEquiv e
  have hm := LiebThirring.spectator_spin_expectation_aemeasurable i u
    (fun z : Position × OtherConfiguration i => p (z.1, E.symm z.2))
    (hp.comp (measurable_fst.prodMk (E.symm.measurable.comp measurable_snd)))
  apply hm.congr
  filter_upwards [] with x
  apply Finset.sum_congr rfl
  intro s _
  exact lintegral_residualStateReindex_weight i e (oneParticleCurrying i u x s)
    (fun y => p (x, y)) (hp.comp (measurable_const.prodMk measurable_id))

/-- Full joint expectation finiteness implies sectorwise residual finiteness almost everywhere. -/
theorem spectator_reindex_joint_expectation_lt_top_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Position × Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p (particlePosition X i, residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      (∫⁻ y : Configuration k,
        p (x, y) * ‖residualParticleSlice i e u x s y‖ₑ ^ 2) < ⊤ := by
  rw [lintegral_spectator_reindex i e u p hp] at hfin
  have hs := ae_lt_top' (spectator_reindex_joint_expectation_aemeasurable i e u p hp) hfin.ne
  filter_upwards [hs] with x hx
  intro s
  exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ s)).trans_lt hx

/-- The literal real joint residual expectation is integrable in the selected position. -/
theorem integrable_spectator_reindex_joint_real {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Position × Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p (particlePosition X i, residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤) :
    Integrable (fun x : Position => ∑ s : Fin q, ∫ y : Configuration k,
      (p (x, y)).toReal * ‖residualParticleSlice i e u x s y‖ ^ 2) := by
  have hslice := spectator_reindex_joint_expectation_lt_top_ae i e u p hp hfin
  have hsum := integrable_toReal_of_lintegral_ne_top
    (spectator_reindex_joint_expectation_aemeasurable i e u p hp)
    (by rw [← lintegral_spectator_reindex i e u p hp]; exact hfin.ne)
  apply hsum.congr
  filter_upwards [hslice] with x hx
  rw [ENNReal.toReal_sum (fun s _ => (hx s).ne)]
  apply Finset.sum_congr rfl
  intro s _
  exact (LiebThirring.integral_weight_norm_sq
    (hp.comp (measurable_const.prodMk measurable_id)).aemeasurable
    (Lp.aestronglyMeasurable (residualParticleSlice i e u x s)) (hx s)).symm

/-- Finite joint quadratic expectations disintegrate as literal real integrals. -/
theorem integral_spectator_reindex_joint_real {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Position × Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N,
      p (particlePosition X i, residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤) :
    (∫ X : Configuration N,
      (p (particlePosition X i, residualProjection i e X)).toReal * ‖u X‖ ^ 2) =
      ∫ x : Position, ∑ s : Fin q, ∫ y : Configuration k,
        (p (x, y)).toReal * ‖residualParticleSlice i e u x s y‖ ^ 2 := by
  have hpfull : Measurable (fun X : Configuration N =>
      p (particlePosition X i, residualProjection i e X)) :=
    hp.comp ((measurable_particlePosition i).prodMk (measurable_residualProjection i e))
  rw [LiebThirring.integral_weight_norm_sq
    (p := fun X : Configuration N => p (particlePosition X i, residualProjection i e X))
    (f := fun X : Configuration N => u X) hpfull.aemeasurable
    (Lp.aestronglyMeasurable u) hfin]
  simp only [← enorm_eq_nnnorm]
  rw [lintegral_spectator_reindex i e u p hp]
  have hslice := spectator_reindex_joint_expectation_lt_top_ae i e u p hp hfin
  have htotal : ∀ᵐ x : Position, (∑ s : Fin q, ∫⁻ y : Configuration k,
      p (x, y) * ‖residualParticleSlice i e u x s y‖ₑ ^ 2) < ⊤ := by
    filter_upwards [hslice] with x hx
    exact ENNReal.sum_lt_top.mpr (fun s _ => hx s)
  rw [← integral_toReal (spectator_reindex_joint_expectation_aemeasurable i e u p hp) htotal]
  apply integral_congr_ae
  filter_upwards [hslice] with x hx
  rw [ENNReal.toReal_sum (fun s _ => (hx s).ne)]
  apply Finset.sum_congr rfl
  intro s _
  exact (LiebThirring.integral_weight_norm_sq
    (hp.comp (measurable_const.prodMk measurable_id)).aemeasurable
    (Lp.aestronglyMeasurable (residualParticleSlice i e u x s)) (hx s)).symm

end LiebThirring.Variational

end
