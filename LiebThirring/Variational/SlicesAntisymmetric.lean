/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesResidual
public import LiebThirring.Kinetic.Permutation

/-!
# Antisymmetry of residual particle slices

A residual permutation is extended by fixing the selected particle. Pulling the original
antisymmetry identity through particle insertion and residual-coordinate reindexing proves that
almost every literal residual slice is antisymmetric.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal Classical
namespace LiebThirring.Variational

noncomputable def extendResidualPerm {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin N) := σ.extendDomain e

@[simp] lemma extendResidualPerm_selected {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (σ : Equiv.Perm (Fin k)) :
    extendResidualPerm i e σ i = i := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp

@[simp] lemma extendResidualPerm_residual {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    extendResidualPerm i e σ (e j) = e (σ j) := by
  exact Equiv.Perm.extendDomain_apply_image σ e j

lemma configurationReindex_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (y : EuclideanSpace ℝ (ι × Fin 3)) (a : ι) (b : Fin 3) :
    Sobolev.configurationReindexMeasurableEquiv e y (e a, b) = y (a, b) := by
  simp only [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply]
  simpa using MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : κ × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) y.ofLp (a, b)

lemma permutePositions_insertParticle_reindex {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (σ : Equiv.Perm (Fin k))
    (x : Position) (y : Configuration k) :
    permutePositions (extendResidualPerm i e σ)
        (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)) =
      insertParticle i x
        (Sobolev.configurationReindexMeasurableEquiv e (permutePositions σ y)) := by
  ext ja
  rcases ja with ⟨j, b⟩
  by_cases hj : j = i
  · subst j
    simp [permutePositions, insertParticle]
  · let a : Fin k := e.symm ⟨j, hj⟩
    have hea : e a = ⟨j, hj⟩ := e.apply_symm_apply ⟨j, hj⟩
    have hval : (e a).val = j := congrArg Subtype.val hea
    have hp : extendResidualPerm i e σ j = (e (σ a)).val := by
      rw [← hval, extendResidualPerm_residual]
    simp only [permutePositions, insertParticle, PiLp.toLp_apply]
    rw [dite_eq_right hj, hp]
    have hne : (e (σ a)).val ≠ i := (e (σ a)).property
    rw [dite_eq_right hne]
    rw [configurationReindex_apply]
    rw [← hea]
    rw [configurationReindex_apply]

lemma permuteSpins_insertSpin_reindex {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (σ : Equiv.Perm (Fin k))
    (s : Fin q) (t : SpinLabels k q) :
    permuteSpins (extendResidualPerm i e σ)
        (insertSpin i s (fun j => t (e.symm j))) =
      insertSpin i s (fun j => permuteSpins σ t (e.symm j)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [permuteSpins]
  · let a : Fin k := e.symm ⟨j, hj⟩
    have hea : e a = ⟨j, hj⟩ := e.apply_symm_apply ⟨j, hj⟩
    have hval : (e a).val = j := congrArg Subtype.val hea
    have hp : extendResidualPerm i e σ j = (e (σ a)).val := by
      rw [← hval, extendResidualPerm_residual]
    rw [permuteSpins, hp, insertSpin_other]
    simp [insertSpin, permuteSpins, hj, a]


theorem residualParticleSlice_antisymmetric_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q) (hu : antisymmetric u) :
    ∀ᵐ x : Position, ∀ s : Fin q, antisymmetric (residualParticleSlice i e u x s) := by
  have hslices := residualParticleSlice_ae i e u
  have hfull (σ : Equiv.Perm (Fin k)) :
      ∀ᵐ z : Position × OtherConfiguration i,
        ∀ t : SpinLabels N q,
          u (permutePositions (extendResidualPerm i e σ) (insertParticle i z.1 z.2))
              (permuteSpins (extendResidualPerm i e σ) t) =
            (((Equiv.Perm.sign (extendResidualPerm i e σ) : ℤˣ) : ℤ) : ℂ) *
              u (insertParticle i z.1 z.2) t :=
    (measurePreserving_insertParticle i).quasiMeasurePreserving.ae
      (hu (extendResidualPerm i e σ))
  have hcurried (σ : Equiv.Perm (Fin k)) :
      ∀ᵐ x : Position, ∀ᵐ y : OtherConfiguration i,
        ∀ t : SpinLabels N q,
          u (permutePositions (extendResidualPerm i e σ) (insertParticle i x y))
              (permuteSpins (extendResidualPerm i e σ) t) =
            (((Equiv.Perm.sign (extendResidualPerm i e σ) : ℤˣ) : ℤ) : ℂ) *
              u (insertParticle i x y) t :=
    Measure.ae_ae_of_ae_prod (hfull σ)
  have hreindexed (σ : Equiv.Perm (Fin k)) :
      ∀ᵐ x : Position, ∀ᵐ y : Configuration k,
        ∀ t : SpinLabels N q,
          u (permutePositions (extendResidualPerm i e σ)
              (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)))
              (permuteSpins (extendResidualPerm i e σ) t) =
            (((Equiv.Perm.sign (extendResidualPerm i e σ) : ℤˣ) : ℤ) : ℂ) *
              u (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)) t := by
    filter_upwards [hcurried σ] with x hx
    exact (Sobolev.measurePreserving_configurationReindex e).quasiMeasurePreserving.ae hx
  have hall : ∀ᵐ x : Position, ∀ σ : Equiv.Perm (Fin k),
      ∀ᵐ y : Configuration k,
        ∀ t : SpinLabels N q,
          u (permutePositions (extendResidualPerm i e σ)
              (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)))
              (permuteSpins (extendResidualPerm i e σ) t) =
            (((Equiv.Perm.sign (extendResidualPerm i e σ) : ℤˣ) : ℤ) : ℂ) *
              u (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y)) t :=
    eventually_countable_forall.mpr hreindexed
  filter_upwards [hslices, hall] with x hx hallx
  intro s σ
  have hxperm := (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae (hx s)
  filter_upwards [hx s, hxperm, hallx σ] with y hy hpy huy
  intro t
  rw [hpy (permuteSpins σ t), hy t]
  have h := huy (insertSpin i s (fun j => t (e.symm j)))
  rw [permutePositions_insertParticle_reindex,
    permuteSpins_insertSpin_reindex] at h
  rw [h]
  have hsign : Equiv.Perm.sign (extendResidualPerm i e σ) = Equiv.Perm.sign σ := by
    unfold extendResidualPerm
    exact Equiv.Perm.sign_extendDomain σ e
  rw [hsign]

end LiebThirring.Variational


end

